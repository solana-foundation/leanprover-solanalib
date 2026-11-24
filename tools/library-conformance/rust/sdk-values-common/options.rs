//! Actual COption calls shared by separately pinned SDK generations.
use conformance_recorder::{self as rec, Corpus, Json, Record};
use crate::{COption, PREFIX, VERSION, PACKAGE, OPTION_CORPUS};
use crate::support::{self as s, Plan, Tracked, Query};

fn function(method: &str) -> &'static str {
    Box::leak(match method {
        "eq" => format!("<{PREFIX}::COption<T> as core::cmp::PartialEq>::eq"),
        "into_option" => format!("{PREFIX}::<impl core::convert::From<{PREFIX}::COption<T>> for core::option::Option<T>>::from"),
        _ => format!("{PREFIX}::COption::<T>::{method}"),
    }.into_boxed_str())
}
fn push(c: &mut Corpus, method: &str, id: String, generics: Vec<(&'static str, &'static str)>, args: Json, state: Json, outcome: Json) {
    c.push(Record { id: format!("{method}/{id}"), function: function(method), generics: generics.into_iter().map(|(k,v)|(k,v.into())).collect(), layout: None, state, args, outcome, observed: None });
}
fn cop<T>(x: &COption<T>, encode: impl Fn(&T) -> Json) -> Json { match x { COption::None => Json::Null, COption::Some(v) => s::some(encode(v)) } }
fn tracked(present: bool, id: u64, value: u64, drop_mode: u8) -> COption<Tracked> {
    if present { COption::Some(Tracked::new(id, value, drop_mode)) } else { COption::None }
}
fn option_json(present: bool, id: u64, value: u64, drop_mode: u8) -> Json {
    if present { s::some(s::tracked_json(id, value, drop_mode)) } else { Json::Null }
}
pub fn record(methods: &[&str]) {
    let mut c = Corpus::new(OPTION_CORPUS, &[(PACKAGE, VERSION)]);
    for &method in methods {
        match method {
            "is_none" | "as_ref" | "into_option" => {
                for (label, v) in [("none", None), ("zero", Some(0)), ("max", Some(u64::MAX))] {
                    let x = v.map(COption::Some).unwrap_or(COption::None);
                    let args = if method == "as_ref" {
                        Json::obj([("parent", 77u64.into()), ("present", v.is_some().into())])
                    } else { Json::obj([("option", cop(&x, |v| (*v).into()))]) };
                    let outcome = match method {
                        "is_none" => rec::returned(x.is_none().into(), Json::Null),
                        "into_option" => { let y: Option<u64> = x.into(); rec::returned(rec::option(&y, |v| (*v).into()), Json::Null) },
                        "as_ref" => {
                            let y = x.as_ref();
                            let result = match (&x, y) {
                                (COption::Some(parent), COption::Some(child)) => s::some(if std::ptr::eq(parent, child) { 77u64 } else { 78u64 }.into()),
                                (_, COption::None) => Json::Null,
                                _ => panic!("returned a reference without a payload"),
                            };
                            rec::returned(result, Json::Null)
                        },
                        _ => unreachable!(),
                    };
                    push(&mut c, method, label.into(), vec![("T", "u64")], args, Json::Null, outcome);
                }
            }
            "eq" => {
                for (left, right, a, b) in [(false,false,7,7),(false,true,7,7),(true,false,7,7),(true,true,7,7),(true,true,7,8)] {
                    for mode in 0..3 {
                        let ids: Vec<u64> = [(left,1),(right,2)].into_iter().filter_map(|(p,i)| p.then_some(i)).collect();
                        let args = Json::obj([("left", option_json(left,1,a,0)),("right",option_json(right,2,b,0)),("mode",(mode as u64).into())]);
                        let outcome = s::case( || {
                            s::reset(Plan { comparison: mode, ..Plan::NORMAL });
                            let x=tracked(left,1,a,0); let y=tracked(right,2,b,0); s::assert_initial(&ids);
                            s::finish(rec::catch(|| x == y), |v| (*v).into())
                        });
                        push(&mut c, method, format!("{left}_{right}_{a}_{b}_{mode}"), vec![("T","Tracked")],args,s::initial(&ids),outcome);
                    }
                }
            }
            "unwrap" => {
                for present in [false,true] {
                    let ids = if present { vec![1] } else { vec![] };
                    let args=Json::obj([("option",option_json(present,1,7,0))]);
                    let outcome=s::case(|| {
                        s::reset(Plan::NORMAL);let x=tracked(present,1,7,0);s::assert_initial(&ids);
                        s::finish(rec::catch(|| x.unwrap()),Tracked::json)
                    });
                    push(&mut c,method,format!("{present}"),vec![("T","Tracked")],args,s::initial(&ids),outcome);
                }
            }
            "map" => {
                for present in [false,true] { for call_mode in 0..3 { for drop_mode in 0..3 {
                    let ids=if present { vec![1,3] } else { vec![3] };
                    let args=Json::obj([("option",option_json(present,1,7,0)),("closure",s::tracked_json(3,5,drop_mode)),("mode",(call_mode as u64).into())]);
                    let outcome=s::case(|| {
                        s::reset(Plan::NORMAL);let x=tracked(present,1,7,0);let capture=Tracked::new(3,5,drop_mode);s::assert_initial(&ids);
                        s::finish(rec::catch(|| x.map(move |value| {
                            s::event(format!("call:{}:{}",capture.id,value.id));
                            let result=value.value.wrapping_add(capture.value);
                            drop(value);drop(capture);s::mode(call_mode,"call".into());result
                        })),|v| cop(v,|v|(*v).into()))
                    });
                    push(&mut c,method,format!("{present}_{call_mode}_{drop_mode}"),vec![("T","Tracked"),("U","u64"),("F","closure")],args,s::initial(&ids),outcome);
                }}}
            }
            "unwrap_or" => {
                for present in [false,true] { for drop_mode in 0..3 {
                    let ids=if present {vec![1,2]} else {vec![2]};
                    let args=Json::obj([("option",option_json(present,1,7,0)),("fallback",s::tracked_json(2,8,drop_mode))]);
                    let outcome=s::case(|| {
                        s::reset(Plan::NORMAL);let x=tracked(present,1,7,0);let fallback=Tracked::new(2,8,drop_mode);s::assert_initial(&ids);
                        s::finish(rec::catch(|| x.unwrap_or(fallback)),Tracked::json)
                    });
                    push(&mut c,method,format!("{present}_{drop_mode}"),vec![("T","Tracked")],args,s::initial(&ids),outcome);
                }}
            }
            "contains" => {
                for present in [false,true] { for query in [3,9] { for mode in 0..3 {
                    let ids=if present {vec![1]} else {vec![]};
                    let args=Json::obj([("option",option_json(present,1,7,0)),("query",Json::obj([("id",2u64.into()),("value",query.into())])),("mode",(mode as u64).into())]);
                    let outcome=s::case(|| {
                        s::reset(Plan {comparison:mode,..Plan::NORMAL});let x=tracked(present,1,7,0);let q=Query{id:2,value:query};s::assert_initial(&ids);
                        s::finish(rec::catch(||x.contains(&q)),|v|(*v).into())
                    });
                    push(&mut c,method,format!("{present}_{query}_{mode}"),vec![("T","Tracked"),("U","Query")],args,s::initial(&ids),outcome);
                }}}
            }
            "unwrap_or_default" => {
                for present in [false,true] { for mode in 0..3 {
                    let ids=if present {vec![1]} else {vec![]};
                    let args=Json::obj([("option",option_json(present,1,7,0)),("mode",(mode as u64).into())]);
                    let outcome=s::case(|| {
                        s::reset(Plan {default:mode,..Plan::NORMAL});let x=tracked(present,1,7,0);s::assert_initial(&ids);
                        s::finish(rec::catch(||x.unwrap_or_default()),Tracked::json)
                    });
                    push(&mut c,method,format!("{present}_{mode}"),vec![("T","Tracked")],args,s::initial(&ids),outcome);
                }}
            }
            _ => panic!("unknown SDK value method"),
        }
    }
    c.write(&rec::out_dir()).expect("write COption corpus");
}
