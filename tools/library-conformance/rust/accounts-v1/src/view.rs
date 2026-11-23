//! solana-account-view 1.0.0: AccountView observations, local mutations,
//! data borrows and the Ref/RefMut guards, over input regions deserialized by
//! `entrypoint::deserialize` in pinocchio 0.10.2.
//!
//! Every record builds a fresh region, deserializes it, runs the setup calls of
//! its scenario (library calls themselves, not recorded), records the state,
//! makes the call under test and records its outcome. The state is the native
//! projection documented in the suite README ("AccountView 1.0.0"):
//!
//! - `accounts`: per non-duplicate account (the cell), the RuntimeAccount header
//!   bytes read back from the region (`borrow_state`, the three flag bytes,
//!   `resize_delta`, `address`, `owner`, `lamports`, `data_len`) and `backing`,
//!   the allocated data area (entry length plus the 10 KiB realloc reserve);
//! - `frame`: the region outside the cell headers and data areas;
//! - `guards`: the live guard objects the driver holds, by identity (the index
//!   of the object in the driver table: creation order, kept by a map), with
//!   the cell and data range they denote, read from the object itself (its
//!   `Debug` output carries its `state` and `value` pointers);
//! - `ghost` (state before only): driver bookkeeping with no native
//!   counterpart, which the model state needs: entry lengths, owner-reference
//!   epochs, the guard-table length and the guard generations.

use crate::region::{self, Account, Entry, Region, HEADER, MAX_PERMITTED_DATA_INCREASE};
use conformance_recorder::{self as rec, Corpus, Json, Record};
use solana_account_view::{AccountView, Ref, RefMut};
use std::mem::MaybeUninit;

const MAX_ACCOUNTS: usize = 8;

pub const F_ADDRESS: &str = "solana_account_view::AccountView::address";
pub const F_CLONE: &str = "<solana_account_view::AccountView as core::clone::Clone>::clone";
pub const F_CLOSE: &str = "solana_account_view::AccountView::close";
pub const F_DATA_LEN: &str = "solana_account_view::AccountView::data_len";
pub const F_IS_DATA_EMPTY: &str = "solana_account_view::AccountView::is_data_empty";
pub const F_IS_SIGNER: &str = "solana_account_view::AccountView::is_signer";
pub const F_IS_WRITABLE: &str = "solana_account_view::AccountView::is_writable";
pub const F_LAMPORTS: &str = "solana_account_view::AccountView::lamports";
pub const F_OWNED_BY: &str = "solana_account_view::AccountView::owned_by";
pub const F_OWNER: &str = "solana_account_view::AccountView::owner";
pub const F_RESIZE: &str = "solana_account_view::AccountView::resize";
pub const F_SET_LAMPORTS: &str = "solana_account_view::AccountView::set_lamports";
pub const F_TRY_BORROW: &str = "solana_account_view::AccountView::try_borrow";
pub const F_TRY_BORROW_MUT: &str = "solana_account_view::AccountView::try_borrow_mut";
pub const F_REF_DEREF: &str = "<solana_account_view::Ref<'_, T> as core::ops::deref::Deref>::deref";
pub const F_REF_MAP: &str = "solana_account_view::Ref::<'a, T>::map";
pub const F_REF_DROP: &str = "<solana_account_view::Ref<'_, T> as core::ops::drop::Drop>::drop";
pub const F_REFMUT_DEREF_MUT: &str =
    "<solana_account_view::RefMut<'_, T> as core::ops::deref::DerefMut>::deref_mut";
pub const F_REFMUT_DROP: &str = "<solana_account_view::RefMut<'_, T> as core::ops::drop::Drop>::drop";

// ---------------------------------------------------------------------------
// Scenarios
// ---------------------------------------------------------------------------

/// Setup calls, made through the library before the state is recorded.
#[derive(Clone, Debug)]
pub enum Setup {
    Borrow(usize),
    BorrowMut(usize),
    /// `Ref::map` of a shared `[u8]` guard to the subrange (offset, length).
    MapSub(usize, usize, usize),
    /// `Ref::map` of a shared `[u8]` guard to its byte at an offset (`Ref<u8>`).
    MapByte(usize, usize),
    Drop(usize),
    SetLamports(usize, u64),
    Resize(usize, usize),
    Close(usize),
    /// Write bytes at an offset through a fresh mutable borrow, then release it.
    Write(usize, usize, Vec<u8>),
    /// Overwrite the `resize_delta` header field directly (forged headers only).
    ForgeResizeDelta(usize, i32),
    /// Overwrite a flag byte (1 signer, 2 writable, 3 executable) directly (forged headers only).
    ForgeFlag(usize, usize, u8),
}

#[derive(Clone, Debug)]
pub struct Scenario {
    pub name: String,
    pub entries: Vec<Entry>,
    pub setup: Vec<Setup>,
}

fn scenario(name: &str, entries: Vec<Entry>, setup: Vec<Setup>) -> Scenario {
    Scenario { name: name.to_string(), entries, setup }
}

/// The map closure script: captured `set_lamports` effects (position, value),
/// then a subrange (offset, length) of its input, or a panic with a message.
#[derive(Clone, Debug)]
pub struct MapScript {
    pub effects: Vec<(usize, u64)>,
    pub exit: MapExit,
}

#[derive(Clone, Debug)]
pub enum MapExit {
    Sub(usize, usize),
    Byte(usize),
    Panic(String),
}

// ---------------------------------------------------------------------------
// Live objects
// ---------------------------------------------------------------------------

enum Obj<'v> {
    Shared(Ref<'v, [u8]>),
    SharedByte(Ref<'v, u8>),
    Exclusive(RefMut<'v, [u8]>),
}

enum Slot<'v> {
    Live(Obj<'v>),
    /// Released by a drop, or consumed by a call that returned no object.
    Gone,
}

struct World<'v> {
    region: &'v Region,
    views: &'v [AccountView],
    slots: Vec<Slot<'v>>,
    generations: Vec<u64>,
    owner_epochs: Vec<u64>,
}

/// The address printed after `field: ` in a guard `Debug` output, and the
/// metadata (slice length) of a wide pointer, which `Debug` prints as
/// `Pointer { addr: 0x.., metadata: n }` in this toolchain.
fn debug_pointer(text: &str, field: &str) -> (usize, Option<usize>) {
    let at = text.find(&format!("{field}: ")).unwrap_or_else(|| panic!("no {field} in {text}")) + field.len() + 2;
    let rest = &text[at..];
    let hex = |s: &str| {
        let s = s.strip_prefix("0x").unwrap_or_else(|| panic!("no address in {s}"));
        let digits: String = s.chars().take_while(|c| c.is_ascii_hexdigit()).collect();
        usize::from_str_radix(&digits, 16).unwrap()
    };
    if let Some(wide) = rest.strip_prefix("Pointer { addr: ") {
        let meta = wide.find("metadata: ").expect("wide pointer metadata") + "metadata: ".len();
        let digits: String = wide[meta..].chars().take_while(|c| c.is_ascii_digit()).collect();
        (hex(wide), Some(digits.parse().unwrap()))
    } else {
        (hex(rest), None)
    }
}

/// (cell, mode, offset, length) of a guard object, read from the
/// `state` and `value` pointers stored in the object (its `Debug` output), without calling
/// any of its methods.
fn object_target(region: &Region, obj: &Obj) -> (usize, &'static str, usize, usize) {
    let (text, mode, thin_len) = match obj {
        Obj::Shared(r) => (format!("{r:?}"), "shared", None),
        Obj::SharedByte(r) => (format!("{r:?}"), "shared", Some(std::mem::size_of::<u8>())),
        Obj::Exclusive(r) => (format!("{r:?}"), "exclusive", None),
    };
    let (state, _) = debug_pointer(&text, "state");
    let (value, meta) = debug_pointer(&text, "value");
    let len = meta.or(thin_len).expect("a slice guard has a wide pointer");
    let cell = region.cell_at_header(state).expect("guard state pointer is a cell's borrow byte");
    let offset = value.checked_sub(region.data_start(cell)).expect("guard target inside its cell");
    (cell, mode, offset, len)
}

fn view_json(offset: usize, length: usize) -> Json {
    Json::obj([("offset", offset.into()), ("length", length.into())])
}

impl<'v> World<'v> {
    fn cell_of_view(&self, view: &AccountView) -> usize {
        self.region
            .cell_at_header(view.account_ptr() as usize)
            .expect("an AccountView denotes a cell of the region")
    }

    fn handle(&self, position: usize) -> usize {
        self.cell_of_view(&self.views[position])
    }

    fn push(&mut self, obj: Obj<'v>) -> usize {
        self.slots.push(Slot::Live(obj));
        self.generations.push(0);
        self.slots.len() - 1
    }

    fn take(&mut self, id: usize) -> Obj<'v> {
        match std::mem::replace(&mut self.slots[id], Slot::Gone) {
            Slot::Live(obj) => obj,
            Slot::Gone => panic!("guard {id} is not live"),
        }
    }

    fn apply(&mut self, step: &Setup) {
        let views = self.views;
        match step {
            Setup::Borrow(p) => {
                let r = views[*p].try_borrow().expect("setup borrow");
                self.push(Obj::Shared(r));
            }
            Setup::BorrowMut(p) => {
                let r = views[*p].try_borrow_mut().expect("setup mutable borrow");
                self.push(Obj::Exclusive(r));
            }
            Setup::MapSub(id, offset, len) => {
                let Obj::Shared(r) = self.take(*id) else { panic!("map of a non-[u8] guard") };
                let (o, l) = (*offset, *len);
                self.slots[*id] = Slot::Live(Obj::Shared(Ref::map(r, |d: &[u8]| &d[o..o + l])));
                self.generations[*id] += 1;
            }
            Setup::MapByte(id, offset) => {
                let Obj::Shared(r) = self.take(*id) else { panic!("map of a non-[u8] guard") };
                let o = *offset;
                self.slots[*id] = Slot::Live(Obj::SharedByte(Ref::map(r, |d: &[u8]| &d[o])));
                self.generations[*id] += 1;
            }
            Setup::Drop(id) => drop(self.take(*id)),
            Setup::SetLamports(p, v) => views[*p].set_lamports(*v),
            Setup::Resize(p, n) => views[*p].resize(*n).expect("setup resize"),
            Setup::Close(p) => {
                views[*p].close().expect("setup close");
                let cell = self.handle(*p);
                self.owner_epochs[cell] += 1;
            }
            Setup::Write(p, offset, bytes) => {
                let mut r = views[*p].try_borrow_mut().expect("setup write borrow");
                r[*offset..*offset + bytes.len()].copy_from_slice(bytes);
            }
            Setup::ForgeResizeDelta(p, delta) => {
                let header = self.region.cells[self.handle(*p)].header;
                self.region.write(header + 4, &delta.to_le_bytes());
            }
            Setup::ForgeFlag(p, index, value) => {
                let header = self.region.cells[self.handle(*p)].header;
                self.region.write(header + index, &[*value]);
            }
        }
    }

    /// The native state; `ghost` adds the bookkeeping for the state before.
    fn state(&self, ghost: bool) -> Json {
        let region = self.region;
        let accounts = Json::arr(region.cells.iter(), |c| {
            let h = c.header;
            let head = region.read(h, HEADER);
            let backing = region.read(h + HEADER, c.entry_len + MAX_PERMITTED_DATA_INCREASE);
            Json::obj([
                ("borrow_state", head[0].into()),
                ("is_signer", head[1].into()),
                ("is_writable", head[2].into()),
                ("executable", head[3].into()),
                ("resize_delta", i32::from_le_bytes(head[4..8].try_into().unwrap()).into()),
                ("address", rec::bytes(&head[8..40])),
                ("owner", rec::bytes(&head[40..72])),
                ("lamports", u64::from_le_bytes(head[72..80].try_into().unwrap()).into()),
                ("data_len", u64::from_le_bytes(head[80..88].try_into().unwrap()).into()),
                ("backing", rec::bytes(&backing)),
            ])
        });
        // Consecutive identities denoting the same target are written as one
        // entry with `"ids": [first, last]` (the 254 shared guards of a saturated cell).
        let mut runs: Vec<(usize, usize, (usize, &str, usize, usize))> = Vec::new();
        for (id, slot) in self.slots.iter().enumerate() {
            if let Slot::Live(obj) = slot {
                let target = object_target(region, obj);
                match runs.last_mut() {
                    Some((_, last, t)) if *last + 1 == id && *t == target => *last = id,
                    _ => runs.push((id, id, target)),
                }
            }
        }
        let guards: Vec<Json> = runs
            .into_iter()
            .map(|(first, last, (cell, mode, offset, length))| {
                let ids = if first == last {
                    ("id".to_string(), first.into())
                } else {
                    ("ids".to_string(), Json::Arr(vec![first.into(), last.into()]))
                };
                Json::Obj(vec![
                    ids,
                    ("cell".to_string(), cell.into()),
                    ("mode".to_string(), mode.into()),
                    ("view".to_string(), view_json(offset, length)),
                ])
            })
            .collect();
        // Everything outside the cell headers and allocated data areas: the
        // account count, alignment padding, rent epochs, duplicate entries,
        // instruction data and program id.
        let projected: Vec<(usize, usize)> =
            (0..region.cells.len()).map(|k| (region.cells[k].header, HEADER + region.capacity(k))).collect();
        let frame = rec::bytes(&region.frame(&projected));
        let mut fields = vec![
            ("accounts".to_string(), accounts),
            ("guards".to_string(), Json::Arr(guards)),
            ("frame".to_string(), frame),
        ];
        if ghost {
            fields.push((
                "ghost".to_string(),
                Json::obj([
                    ("entry_len", Json::arr(region.cells.iter(), |c| c.entry_len.into())),
                    ("owner_epoch", Json::arr(self.owner_epochs.iter(), |e| (*e).into())),
                    ("slots", self.slots.len().into()),
                    ("generations", Json::arr(self.generations.iter(), |g| (*g).into())),
                ]),
            ));
        }
        Json::Obj(fields)
    }

    /// The target of a reference returned by a dereference: its cell, range and bytes.
    fn reference_json(&self, address: usize, length: usize, bytes: &[u8], writable: bool) -> Json {
        let (cell, offset) = self.region.locate_data(address).expect("reference into a cell's data");
        Json::obj([
            ("cell", cell.into()),
            ("view", view_json(offset, length)),
            ("bytes", rec::bytes(bytes)),
            ("writable", writable.into()),
        ])
    }

    /// A reference to a header field: its cell, the field offset in the header and its bytes.
    fn field_json(&self, address: usize, bytes: &[u8]) -> Json {
        let (cell, field) = self.region.locate_header(address).expect("reference into a cell's header");
        Json::obj([("cell", cell.into()), ("field", field.into()), ("bytes", rec::bytes(bytes))])
    }
}

fn program_error(e: &solana_program_error::ProgramError) -> Json {
    format!("{e:?}").into()
}

fn unit_result(r: &Result<(), solana_program_error::ProgramError>) -> Json {
    match r {
        Ok(()) => rec::ok(Json::Null),
        Err(e) => rec::err(program_error(e)),
    }
}

// ---------------------------------------------------------------------------
// Calls under test
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
pub enum Call {
    Lamports(usize),
    DataLen(usize),
    IsDataEmpty(usize),
    IsSigner(usize),
    IsWritable(usize),
    Clone(usize),
    Address(usize),
    Owner(usize),
    OwnedBy(usize, [u8; 32]),
    SetLamports(usize, u64),
    TryBorrow(usize),
    TryBorrowMut(usize),
    Resize(usize, usize),
    Close(usize),
    Deref(usize),
    DerefMut(usize),
    Release(usize),
    Map(usize, MapScript),
}

struct Called {
    function: &'static str,
    generics: Vec<(&'static str, String)>,
    args: Json,
    observed: Json,
    outcome: Json,
}

fn generic_t(world: &World, id: usize) -> Vec<(&'static str, String)> {
    match &world.slots[id] {
        Slot::Live(Obj::SharedByte(_)) => vec![("T", "u8".to_string())],
        _ => vec![("T", "[u8]".to_string())],
    }
}

fn run<'v>(world: &mut World<'v>, call: &Call) -> Called {
    let views = world.views;
    let handle_args = |w: &World, p: usize| Json::obj([("handle", w.handle(p).into())]);
    let observed_position = |p: usize| Json::obj([("position", p.into())]);
    // Calls without a guard argument.
    macro_rules! simple {
        ($f:expr, $p:expr, $args:expr, $body:expr) => {{
            let args = $args;
            let result = rec::catch(|| $body);
            let outcome = match result {
                Ok(v) => rec::returned(v, world.state(false)),
                Err(reason) => rec::unwound(reason, world.state(false)),
            };
            Called { function: $f, generics: vec![], args, observed: observed_position($p), outcome }
        }};
    }
    match call {
        Call::Lamports(p) => simple!(F_LAMPORTS, *p, handle_args(world, *p), Json::from(views[*p].lamports())),
        Call::DataLen(p) => simple!(F_DATA_LEN, *p, handle_args(world, *p), Json::from(views[*p].data_len())),
        Call::IsDataEmpty(p) => {
            simple!(F_IS_DATA_EMPTY, *p, handle_args(world, *p), Json::from(views[*p].is_data_empty()))
        }
        Call::IsSigner(p) => simple!(F_IS_SIGNER, *p, handle_args(world, *p), Json::from(views[*p].is_signer())),
        Call::IsWritable(p) => {
            simple!(F_IS_WRITABLE, *p, handle_args(world, *p), Json::from(views[*p].is_writable()))
        }
        Call::Clone(p) => {
            let args = handle_args(world, *p);
            let result = rec::catch(|| views[*p].clone());
            let outcome = match result {
                Ok(v) => {
                    let cell = world.cell_of_view(&v);
                    rec::returned(Json::obj([("cell", cell.into())]), world.state(false))
                }
                Err(reason) => rec::unwound(reason, world.state(false)),
            };
            Called { function: F_CLONE, generics: vec![], args, observed: observed_position(*p), outcome }
        }
        Call::Address(p) => {
            let args = handle_args(world, *p);
            let result = rec::catch(|| views[*p].address() as *const _ as usize);
            let outcome = match result {
                Ok(address) => {
                    let bytes = world.region.read(address - world.region.base() as usize, 32);
                    rec::returned(world.field_json(address, &bytes), world.state(false))
                }
                Err(reason) => rec::unwound(reason, world.state(false)),
            };
            Called { function: F_ADDRESS, generics: vec![], args, observed: observed_position(*p), outcome }
        }
        Call::Owner(p) => {
            let args = handle_args(world, *p);
            // SAFETY: the reference is not used after any owner change.
            let result = rec::catch(|| unsafe { views[*p].owner() } as *const _ as usize);
            let outcome = match result {
                Ok(address) => {
                    let bytes = world.region.read(address - world.region.base() as usize, 32);
                    rec::returned(world.field_json(address, &bytes), world.state(false))
                }
                Err(reason) => rec::unwound(reason, world.state(false)),
            };
            Called { function: F_OWNER, generics: vec![], args, observed: observed_position(*p), outcome }
        }
        Call::OwnedBy(p, program) => {
            let args = Json::obj([("handle", world.handle(*p).into()), ("program", rec::bytes(program))]);
            let address = pinocchio::Address::new_from_array(*program);
            let result = rec::catch(|| views[*p].owned_by(&address));
            let outcome = match result {
                Ok(v) => rec::returned(v.into(), world.state(false)),
                Err(reason) => rec::unwound(reason, world.state(false)),
            };
            Called { function: F_OWNED_BY, generics: vec![], args, observed: observed_position(*p), outcome }
        }
        Call::SetLamports(p, value) => simple!(
            F_SET_LAMPORTS,
            *p,
            Json::obj([("handle", world.handle(*p).into()), ("lamports", (*value).into())]),
            {
                views[*p].set_lamports(*value);
                Json::Null
            }
        ),
        Call::TryBorrow(p) | Call::TryBorrowMut(p) => {
            let shared = matches!(call, Call::TryBorrow(_));
            let args = handle_args(world, *p);
            let result = rec::catch(|| {
                if shared {
                    views[*p].try_borrow().map(Obj::Shared)
                } else {
                    views[*p].try_borrow_mut().map(Obj::Exclusive)
                }
            });
            let outcome = match result {
                Ok(Ok(obj)) => {
                    let id = world.push(obj);
                    rec::returned(rec::ok(Json::obj([("guard", id.into())])), world.state(false))
                }
                Ok(Err(e)) => rec::returned(rec::err(program_error(&e)), world.state(false)),
                Err(reason) => rec::unwound(reason, world.state(false)),
            };
            let function = if shared { F_TRY_BORROW } else { F_TRY_BORROW_MUT };
            Called { function, generics: vec![], args, observed: observed_position(*p), outcome }
        }
        Call::Resize(p, n) => {
            let args = Json::obj([("handle", world.handle(*p).into()), ("new_len", (*n).into())]);
            let result = rec::catch(|| views[*p].resize(*n));
            let outcome = match result {
                Ok(r) => rec::returned(unit_result(&r), world.state(false)),
                Err(reason) => rec::unwound(reason, world.state(false)),
            };
            Called { function: F_RESIZE, generics: vec![], args, observed: observed_position(*p), outcome }
        }
        Call::Close(p) => {
            let args = handle_args(world, *p);
            let result = rec::catch(|| views[*p].close());
            let outcome = match result {
                Ok(r) => rec::returned(unit_result(&r), world.state(false)),
                Err(reason) => rec::unwound(reason, world.state(false)),
            };
            Called { function: F_CLOSE, generics: vec![], args, observed: observed_position(*p), outcome }
        }
        Call::Deref(id) | Call::DerefMut(id) => {
            let generics = generic_t(world, *id);
            let args = Json::obj([("guard", (*id).into())]);
            let mutable = matches!(call, Call::DerefMut(_));
            let result = {
                let Slot::Live(obj) = &mut world.slots[*id] else { panic!("dereference of a dead guard") };
                rec::catch(|| match obj {
                    Obj::Shared(r) => {
                        let d: &[u8] = &**r;
                        (d.as_ptr() as usize, d.len(), d.to_vec())
                    }
                    Obj::SharedByte(r) => {
                        let d: &u8 = &**r;
                        (d as *const u8 as usize, 1, vec![*d])
                    }
                    Obj::Exclusive(r) => {
                        if mutable {
                            let d: &mut [u8] = &mut **r;
                            (d.as_ptr() as usize, d.len(), d.to_vec())
                        } else {
                            panic!("RefMut::deref is not a recorded call")
                        }
                    }
                })
            };
            let outcome = match result {
                Ok((address, len, bytes)) => {
                    let value = world.reference_json(address, len, &bytes, mutable);
                    rec::returned(value, world.state(false))
                }
                Err(reason) => rec::unwound(reason, world.state(false)),
            };
            let function = if mutable { F_REFMUT_DEREF_MUT } else { F_REF_DEREF };
            Called { function, generics, args, observed: Json::Null, outcome }
        }
        Call::Release(id) => {
            let generics = generic_t(world, *id);
            let args = Json::obj([("guard", (*id).into())]);
            let obj = world.take(*id);
            let function = match obj {
                Obj::Exclusive(_) => F_REFMUT_DROP,
                _ => F_REF_DROP,
            };
            let result = rec::catch(move || drop(obj));
            let outcome = match result {
                Ok(()) => rec::returned(Json::Null, world.state(false)),
                Err(reason) => rec::unwound(reason, world.state(false)),
            };
            Called { function, generics, args, observed: Json::Null, outcome }
        }
        Call::Map(id, script) => {
            let Obj::Shared(r) = world.take(*id) else { panic!("map of a non-[u8] guard") };
            let effects: Vec<Json> = script
                .effects
                .iter()
                .map(|(p, v)| Json::obj([("handle", world.handle(*p).into()), ("lamports", (*v).into())]))
                .collect();
            let (exit, u) = match &script.exit {
                MapExit::Sub(o, l) => (Json::obj([("return", view_json(*o, *l))]), "[u8]"),
                MapExit::Byte(o) => (Json::obj([("return", view_json(*o, 1))]), "u8"),
                MapExit::Panic(m) => (Json::obj([("panic", m.as_str().into())]), "[u8]"),
            };
            let args = Json::obj([
                ("guard", (*id).into()),
                ("callback", Json::obj([("effects", Json::Arr(effects)), ("exit", exit)])),
            ]);
            let generics = vec![("T", "[u8]".to_string()), ("U", u.to_string()), ("F", "scripted closure".to_string())];
            let effects = script.effects.clone();
            let exit = script.exit.clone();
            let result = rec::catch(move || {
                let apply = |d: &[u8]| {
                    for (p, v) in &effects {
                        views[*p].set_lamports(*v);
                    }
                    let _ = d;
                };
                match exit {
                    MapExit::Sub(o, l) => Obj::Shared(Ref::map(r, |d: &[u8]| {
                        apply(d);
                        &d[o..o + l]
                    })),
                    MapExit::Byte(o) => Obj::SharedByte(Ref::map(r, |d: &[u8]| {
                        apply(d);
                        &d[o]
                    })),
                    MapExit::Panic(m) => Obj::Shared(Ref::map(r, |d: &[u8]| -> &[u8] {
                        apply(d);
                        panic!("{m}")
                    })),
                }
            });
            let outcome = match result {
                Ok(obj) => {
                    world.slots[*id] = Slot::Live(obj);
                    world.generations[*id] += 1;
                    rec::returned(Json::obj([("guard", (*id).into())]), world.state(false))
                }
                Err(reason) => rec::unwound(reason, world.state(false)),
            };
            Called { function: F_REF_MAP, generics, args, observed: Json::Null, outcome }
        }
    }
}

/// Deserialize the region with pinocchio 0.10.2 and run one call.
pub fn record_case(c: &mut Corpus, id: &str, sc: &Scenario, call: &Call) {
    let region = Region::new(&region::input(sc.entries.clone()));
    let mut raw: [MaybeUninit<AccountView>; MAX_ACCOUNTS] = [const { MaybeUninit::uninit() }; MAX_ACCOUNTS];
    // SAFETY: the region is laid out as the loader serializes it and outlives the views.
    let (_, count, _) = unsafe { pinocchio::entrypoint::deserialize::<MAX_ACCOUNTS>(region.base(), &mut raw) };
    assert_eq!(count, sc.entries.len());
    // SAFETY: `deserialize` initialized the first `count` views.
    let views: Vec<AccountView> = raw[..count].iter().map(|v| unsafe { v.assume_init_read() }).collect();
    let mut world = World {
        region: &region,
        views: &views,
        slots: Vec::new(),
        generations: Vec::new(),
        owner_epochs: vec![0; region.cells.len()],
    };
    for step in &sc.setup {
        world.apply(step);
    }
    let before = world.state(true);
    let called = run(&mut world, call);
    c.push(Record {
        id: format!("{}/{}", sc.name, id),
        function: called.function,
        generics: called.generics,
        layout: None,
        state: before,
        args: called.args,
        outcome: called.outcome,
        observed: if called.observed == Json::Null { None } else { Some(called.observed) },
    });
    drop(world);
}

// ---------------------------------------------------------------------------
// Case selection
// ---------------------------------------------------------------------------

fn acct(seed: u8, lamports: u64, len: usize) -> Account {
    region::account(seed, lamports, len)
}

fn flags(mut a: Account, signer: bool, writable: bool, executable: bool) -> Account {
    a.is_signer = signer;
    a.is_writable = writable;
    a.executable = executable;
    a
}

/// Regions: a single account, several accounts with duplicates, empty data.
fn regions() -> Vec<(&'static str, Vec<Entry>)> {
    use Entry::{Account as A, Duplicate as Dup};
    vec![
        ("one", vec![A(acct(1, 1_000, 16))]),
        ("empty", vec![A(flags(acct(2, 0, 0), true, false, true))]),
        (
            "dups",
            vec![
                A(flags(acct(3, 5_000, 8), true, true, false)),
                A(flags(acct(4, u64::MAX, 3), false, false, false)),
                Dup(0),
                A(flags(acct(5, 1, 5), true, false, true)),
                Dup(1),
            ],
        ),
    ]
}

/// The scenarios: borrow states reachable through the library (free, shared,
/// the 253rd and 254th shared guard, exclusive, through an alias, released,
/// mapped) and data states (shrunk with a hidden nonzero suffix, grown, at the
/// growth limit, closed, written then shrunk, an empty account grown).
fn scenarios() -> Vec<Scenario> {
    use Setup::*;
    let region = |name: &str| regions().into_iter().find(|(n, _)| *n == name).unwrap().1;
    let shared = |k: usize| (0..k).map(|_| Borrow(0)).collect::<Vec<_>>();
    vec![
        scenario("one/free", region("one"), vec![]),
        scenario("one/shared1", region("one"), shared(1)),
        scenario("one/shared253", region("one"), shared(253)),
        scenario("one/shared254", region("one"), shared(254)),
        scenario("one/exclusive", region("one"), vec![BorrowMut(0)]),
        scenario("one/released", region("one"), vec![Borrow(0), Borrow(0), Drop(0)]),
        scenario("one/released-mut", region("one"), vec![BorrowMut(0), Drop(0)]),
        scenario("one/mapped", region("one"), vec![Borrow(0), MapSub(0, 4, 8)]),
        scenario("one/mapped-byte", region("one"), vec![Borrow(0), Borrow(0), MapByte(1, 3)]),
        scenario("one/shrunk", region("one"), vec![Resize(0, 5)]),
        scenario("one/grown", region("one"), vec![Resize(0, 100)]),
        scenario("one/at-limit", region("one"), vec![Resize(0, 16 + MAX_PERMITTED_DATA_INCREASE)]),
        scenario("one/closed", region("one"), vec![SetLamports(0, 0), Close(0)]),
        scenario("one/written", region("one"), vec![Write(0, 2, vec![0, 0, 0xee]), Resize(0, 3)]),
        scenario("empty/free", region("empty"), vec![]),
        scenario("empty/shared1", region("empty"), vec![Borrow(0)]),
        scenario("empty/exclusive", region("empty"), vec![BorrowMut(0)]),
        scenario("empty/grown", region("empty"), vec![Resize(0, 7), Write(0, 0, vec![9; 7])]),
        scenario("dups/free", region("dups"), vec![]),
        scenario("dups/alias-shared", region("dups"), vec![Borrow(2), Borrow(0)]),
        scenario("dups/alias-exclusive", region("dups"), vec![BorrowMut(4)]),
        scenario("dups/other-exclusive", region("dups"), vec![BorrowMut(1), Borrow(3)]),
    ]
}

/// Case selection (the README rule): per instantiation, one or two inputs of
/// every outcome class, boundary values and every borrow and data state that
/// changes the outcome or the state after, at most about twenty.
pub fn record(c: &mut Corpus) {
    let all = scenarios();
    let sc = |name: &str| all.iter().find(|s| s.name == name).unwrap_or_else(|| panic!("no scenario {name}"));
    let entry = 16usize;
    let mut case = |name: &str, tag: &str, call: Call| record_case(c, tag, sc(name), &call);

    // Observations: every account and alias of the duplicate region, an empty
    // account, a held exclusive guard, shrunk and closed accounts.
    // (Position 1 is observed through its alias at position 4.)
    let observed: [(&str, usize); 8] = [
        ("dups/free", 0),
        ("dups/free", 2),
        ("dups/free", 3),
        ("dups/free", 4),
        ("empty/free", 0),
        ("one/exclusive", 0),
        ("one/shrunk", 0),
        ("one/closed", 0),
    ];
    for (name, p) in observed {
        let tag = |what: &str| format!("{what}/p{p}");
        case(name, &tag("lamports"), Call::Lamports(p));
        case(name, &tag("data_len"), Call::DataLen(p));
        case(name, &tag("is_data_empty"), Call::IsDataEmpty(p));
        case(name, &tag("is_signer"), Call::IsSigner(p));
        case(name, &tag("is_writable"), Call::IsWritable(p));
        case(name, &tag("clone"), Call::Clone(p));
        case(name, &tag("address"), Call::Address(p));
        case(name, &tag("owner"), Call::Owner(p));
    }

    // Owner comparison: equal, another owner, one bit off, zero; an alias; a closed account.
    let own = region::key(101);
    let mut near = own;
    near[31] ^= 1;
    case("one/free", "owned_by/own", Call::OwnedBy(0, own));
    case("one/free", "owned_by/other", Call::OwnedBy(0, region::key(55)));
    case("one/free", "owned_by/one-bit", Call::OwnedBy(0, near));
    case("one/free", "owned_by/zero", Call::OwnedBy(0, [0; 32]));
    case("dups/free", "owned_by/alias/p4", Call::OwnedBy(4, region::key(104)));
    case("one/closed", "owned_by/zero", Call::OwnedBy(0, [0; 32]));

    // Balance write: boundary values, unchanged, through an alias, during borrows.
    for (tag, v) in [("zero", 0u64), ("one", 1), ("max", u64::MAX), ("same", 1_000)] {
        case("one/free", &format!("set_lamports/{tag}"), Call::SetLamports(0, v));
    }
    case("dups/free", "set_lamports/alias/p2", Call::SetLamports(2, 7));
    case("one/shared1", "set_lamports/max", Call::SetLamports(0, u64::MAX));
    case("one/exclusive", "set_lamports/max", Call::SetLamports(0, u64::MAX));

    // Shared borrow: success (fresh, beside shared guards, the 254th), failure
    // (saturated, exclusive, exclusive through an alias), beside an exclusive
    // guard on another account, after releases, of a mapped account, of empty data.
    for (name, p) in [
        ("one/free", 0),
        ("one/shared1", 0),
        ("one/shared253", 0),
        ("one/shared254", 0),
        ("one/exclusive", 0),
        ("dups/alias-exclusive", 1),
        ("dups/alias-exclusive", 0),
        ("dups/other-exclusive", 3),
        ("one/released", 0),
        ("one/released-mut", 0),
        ("one/mapped", 0),
        ("empty/free", 0),
        ("one/closed", 0),
    ] {
        case(name, &format!("try_borrow/p{p}"), Call::TryBorrow(p));
    }
    // Exclusive borrow: success, failure on shared, exclusive, saturated and
    // aliased guards, beside guards on another account, after releases, mapped.
    for (name, p) in [
        ("one/free", 0),
        ("one/shared1", 0),
        ("one/shared254", 0),
        ("one/exclusive", 0),
        ("dups/alias-shared", 2),
        ("dups/alias-shared", 1),
        ("dups/other-exclusive", 0),
        ("one/released", 0),
        ("one/released-mut", 0),
        ("one/mapped", 0),
        ("empty/free", 0),
        ("one/grown", 0),
    ] {
        case(name, &format!("try_borrow_mut/p{p}"), Call::TryBorrowMut(p));
    }
    // Close: success on free accounts (also after resizes and a close), through
    // an alias; failure on shared, exclusive, aliased, mapped and released-once guards.
    for (name, p) in [
        ("one/free", 0),
        ("one/shrunk", 0),
        ("one/grown", 0),
        ("one/at-limit", 0),
        ("one/closed", 0),
        ("empty/free", 0),
        ("dups/free", 2),
        ("one/shared1", 0),
        ("one/exclusive", 0),
        ("dups/alias-exclusive", 1),
        ("dups/alias-exclusive", 0),
        ("one/mapped", 0),
        ("one/released", 0),
        ("one/released-mut", 0),
    ] {
        case(name, &format!("close/p{p}"), Call::Close(p));
    }
    // Resize: shrink, unchanged, grow, the growth limit, the i32 conversion,
    // regrowth over a hidden suffix, growth after close, borrow precedence.
    let limit = entry + MAX_PERMITTED_DATA_INCREASE;
    for (name, tag, p, n) in [
        ("one/free", "zero", 0, 0usize),
        ("one/free", "one", 0, 1),
        ("one/free", "entry", 0, entry),
        ("one/free", "entry+1", 0, entry + 1),
        ("one/free", "limit", 0, limit),
        ("one/free", "limit+1", 0, limit + 1),
        ("one/free", "i32max", 0, i32::MAX as usize),
        ("one/free", "i32max+1", 0, i32::MAX as usize + 1),
        ("one/free", "usizemax", 0, usize::MAX),
        ("one/shrunk", "entry", 0, entry),
        ("one/shrunk", "limit", 0, limit),
        ("one/written", "entry", 0, entry),
        ("one/grown", "one", 0, 1),
        ("one/at-limit", "limit+1", 0, limit + 1),
        ("one/closed", "entry+1", 0, entry + 1),
        ("one/closed", "limit+1", 0, limit + 1),
        ("empty/free", "one", 0, 1),
        ("dups/free", "alias", 2, 9),
        ("one/shared1", "entry", 0, entry),
        ("one/exclusive", "i32max+1", 0, i32::MAX as usize + 1),
    ] {
        case(name, &format!("resize/{tag}"), Call::Resize(p, n));
    }

    // Guards: dereference (a whole range, a mapped range, a mapped byte, an
    // alias, after a release, empty data), release (the last shared guard, one
    // of two, one of 254, a mapped guard, a mapped byte; exclusive guards).
    for (name, id) in [
        ("one/shared1", 0),
        ("one/mapped", 0),
        ("one/mapped-byte", 1),
        ("dups/alias-shared", 0),
        ("one/released", 1),
        ("empty/shared1", 0),
    ] {
        case(name, &format!("deref/g{id}"), Call::Deref(id));
    }
    for (name, id) in [("one/exclusive", 0), ("dups/alias-exclusive", 0), ("empty/exclusive", 0)] {
        case(name, &format!("deref_mut/g{id}"), Call::DerefMut(id));
        case(name, &format!("release/g{id}"), Call::Release(id));
    }
    for (name, id) in [
        ("one/shared1", 0),
        ("dups/alias-shared", 1),
        ("one/shared254", 253),
        ("one/mapped", 0),
        ("one/mapped-byte", 1),
        ("one/mapped-byte", 0),
    ] {
        case(name, &format!("release/g{id}"), Call::Release(id));
    }
    drop(case);
    map_cases(c, &all);
}

/// Live guards after scenario setup: id and kind ('s' shared `[u8]`,
/// 'b' shared `u8`, 'e' exclusive).
#[allow(dead_code)]
fn live_guards(sc: &Scenario) -> Vec<(usize, char)> {
    let mut slots: Vec<Option<char>> = Vec::new();
    for step in &sc.setup {
        match step {
            Setup::Borrow(_) => slots.push(Some('s')),
            Setup::BorrowMut(_) => slots.push(Some('e')),
            Setup::MapByte(id, _) => slots[*id] = Some('b'),
            Setup::Drop(id) => slots[*id] = None,
            _ => {}
        }
    }
    slots.iter().enumerate().filter_map(|(i, s)| s.map(|k| (i, k))).collect()
}

/// The current length of a live `[u8]` guard after scenario setup, read natively.
fn guard_len(sc: &Scenario, id: usize) -> usize {
    let region = Region::new(&region::input(sc.entries.clone()));
    let mut raw: [MaybeUninit<AccountView>; MAX_ACCOUNTS] = [const { MaybeUninit::uninit() }; MAX_ACCOUNTS];
    // SAFETY: as in `record_case`.
    let (_, count, _) = unsafe { pinocchio::entrypoint::deserialize::<MAX_ACCOUNTS>(region.base(), &mut raw) };
    // SAFETY: `deserialize` initialized the first `count` views.
    let views: Vec<AccountView> = raw[..count].iter().map(|v| unsafe { v.assume_init_read() }).collect();
    let mut world = World {
        region: &region,
        views: &views,
        slots: Vec::new(),
        generations: Vec::new(),
        owner_epochs: vec![0; region.cells.len()],
    };
    for step in &sc.setup {
        world.apply(step);
    }
    let Slot::Live(obj) = &world.slots[id] else { panic!("guard {id} is not live") };
    object_target(&region, obj).3
}

/// `Ref::map` with scripted closures: the whole range, an empty range at the
/// end, a middle range, one byte (`U = u8`), captured `set_lamports` effects on
/// the held and on another account, a panic with and without effects; and
/// mapping an already mapped guard, an aliased guard, the 254th guard, empty data.
fn map_cases(c: &mut Corpus, all: &[Scenario]) {
    let sc = |name: &str| all.iter().find(|s| s.name == name).unwrap();
    let ret = |o: usize, l: usize| MapScript { effects: vec![], exit: MapExit::Sub(o, l) };
    let panic = |effects: Vec<(usize, u64)>| MapScript { effects, exit: MapExit::Panic("scripted closure panic".into()) };
    let one = sc("one/shared1");
    let len = guard_len(one, 0);
    record_case(c, "map/g0/identity", one, &Call::Map(0, ret(0, len)));
    record_case(c, "map/g0/empty-end", one, &Call::Map(0, ret(len, 0)));
    record_case(c, "map/g0/middle", one, &Call::Map(0, ret(1, len - 2)));
    record_case(c, "map/g0/byte", one, &Call::Map(0, MapScript { effects: vec![], exit: MapExit::Byte(len - 1) }));
    record_case(c, "map/g0/effects", one, &Call::Map(0, MapScript { effects: vec![(0, 42)], exit: MapExit::Sub(0, 2) }));
    record_case(c, "map/g0/panic", one, &Call::Map(0, panic(vec![])));
    record_case(c, "map/g0/effects-panic", one, &Call::Map(0, panic(vec![(0, 42), (0, 7)])));
    let mapped = sc("one/mapped");
    let len = guard_len(mapped, 0);
    record_case(c, "map/g0/middle", mapped, &Call::Map(0, ret(1, len - 2)));
    let alias = sc("dups/alias-shared");
    record_case(
        c,
        "map/g0/effects-other",
        alias,
        &Call::Map(0, MapScript { effects: vec![(1, 9), (4, 11)], exit: MapExit::Byte(0) }),
    );
    record_case(c, "map/g1/effects-panic", alias, &Call::Map(1, panic(vec![(3, 0)])));
    let full = sc("one/shared254");
    record_case(c, "map/g253/middle", full, &Call::Map(253, ret(2, 3)));
    let empty = sc("empty/shared1");
    record_case(c, "map/g0/identity", empty, &Call::Map(0, ret(0, 0)));
}

/// Headers the loader cannot produce: a `resize_delta` near the `i32` bounds
/// and flag bytes other than 0 and 1.
pub fn record_forged(c: &mut Corpus) {
    let (_, one) = regions().remove(0);
    let near_max = scenario("forged/delta-near-max", one.clone(), vec![Setup::ForgeResizeDelta(0, i32::MAX - 5)]);
    for (tag, n) in [("shrink", 4usize), ("grow", 32), ("unchanged", 16)] {
        record_case(c, &format!("resize/{tag}"), &near_max, &Call::Resize(0, n));
    }
    record_case(c, "close", &near_max, &Call::Close(0));
    let near_min = scenario("forged/delta-near-min", one.clone(), vec![Setup::ForgeResizeDelta(0, i32::MIN + 5)]);
    for (tag, n) in [("shrink", 4usize), ("grow", 32), ("unchanged", 16)] {
        record_case(c, &format!("resize/{tag}"), &near_min, &Call::Resize(0, n));
    }
    record_case(c, "close", &near_min, &Call::Close(0));
    let large = scenario("forged/delta-large", one.clone(), vec![Setup::ForgeResizeDelta(0, 20_000)]);
    for (tag, n) in [("shrink", 4usize), ("grow", 17)] {
        record_case(c, &format!("resize/{tag}"), &large, &Call::Resize(0, n));
    }
    for value in [2u8, 0xff] {
        let sc = scenario(
            &format!("forged/flags-{value:02x}"),
            one.clone(),
            vec![Setup::ForgeFlag(0, 1, value), Setup::ForgeFlag(0, 2, value), Setup::ForgeFlag(0, 3, value)],
        );
        record_case(c, "is_signer", &sc, &Call::IsSigner(0));
        record_case(c, "is_writable", &sc, &Call::IsWritable(0));
        if value == 2 {
            // The raw flag bytes survive a header write.
            record_case(c, "set_lamports", &sc, &Call::SetLamports(0, 9));
        }
    }
}
