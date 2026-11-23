"""Lifecycle replay must reject changes to effects, callback order and ownership.

The generic runner separately corrupts the result and account
backing of every function. These controls target lifecycle-specific observations, including
partial effects before an error or unwind. Native source and corpus stay intact.
"""

from common import hex_bytes, hex_text, on_record


def state(record):
    return record['outcome']['state']


def rc_count(record):
    state(record)['ref_counts'][0][1] += 1


def callback_rc(record):
    state(record)['log'][0]['ref_counts'][0] += 1


def callback_order(record):
    state(record)['log'].reverse()


def callback_lease(record):
    state(record)['log'][-1]['leases'][1] = 'exclusive'


def decoder_method(record):
    event = next(event for event in state(record)['log'] if event['call'].startswith('deserialize'))
    event['call'] = 'deserialize' if event['call'] == 'deserialize_unchecked' else 'deserialize_unchecked'


def decoder_input(record):
    event = next(event for event in state(record)['log'] if event['call'].startswith('deserialize'))
    event['argument'] = 'ff' + event['argument'][2:]


def decoder_guard(record):
    event = next(event for event in state(record)['log'] if event['call'].startswith('deserialize'))
    event['leases'][1] = 'free'


def saved_payload(record):
    state(record)['payload'] = 11


def remaining(record):
    state(record)['remaining'] = [0]


def bump(record):
    current = state(record)['bumps']
    if isinstance(current, list):
        current[0][1] += 1
    else:
        state(record)['bumps'] += 1


def realloc(record):
    state(record)['reallocs'] = []


def original_record(record):
    event = next(event for event in state(record)['log'] if event['call'] == 'from_account_info')
    event['argument'] = 0


def error_lifetime(record):
    state(record)['fresh_live'] += 1


def owned_string(record):
    state(record)['program_string_dropped'] = False


def data_not_written(record):
    state(record)['input']['accounts'][0]['data'] = record['state']['input']['accounts'][0]['data']


def write_count(record):
    event = next(event for event in state(record)['log'] if event['call'] == 'write')
    event['argument'] += 1


def memcpy_input(record):
    request = state(record)['syscalls']['log'][0]
    data = bytearray(hex_bytes(request['bytes']))
    data[0] ^= 1
    request['bytes'] = hex_text(bytes(data))


def unexpected_memcpy(record):
    state(record)['syscalls']['log'].append({'syscall': 'sol_memcpy_', 'bytes': ''})


def error_text(record):
    record['outcome']['result']['err']['AnchorError']['message'] += '!'


def closed_owner(record):
    state(record)['input']['accounts'][0]['owner'] = '77' * 32


def credited_lamports(record):
    state(record)['input']['accounts'][1]['lamports'] -= 1


def final_lease(record):
    state(record)['leases'][1] = 'shared'


# Every group has a checked or unchecked constructor. The exact primary model
# registrations differ across releases, so their explicitly observed objects
# are kept here rather than treating all versions as one name-only function.
VERSIONS = ('0_27_0', '0_29_0', '0_32_1', '1_0_2', '1_1_2')
CONTROLS = []


def add(version, label, record_id, mutation):
    CONTROLS.append((label, 'anchor_lifecycle_' + version, on_record(record_id, mutation)))


for version in VERSIONS:
    obj = 'interface_account' if version == '1_0_2' else 'account'
    add(version, 'remaining input consumed exactly once', obj + '/try_accounts/ok', remaining)
    add(version, 'failed leaf constructor keeps its consumed tail', obj + '/try_accounts/decoder_error', remaining)
    add(version, 'unwinding leaf constructor keeps its consumed tail', obj + '/try_accounts/decoder_unwinds_with_effects', remaining)
    add(version, 'Rc owner count at return', obj + '/try_accounts/ok', rc_count)
    add(version, 'Rc owner count during callback', obj + '/try_accounts/ok', callback_rc)
    add(version, 'checked decoder receives the whole slice', obj + '/try_accounts/ok', decoder_input)
    add(version, 'checked decoder holds its shared borrow', obj + '/try_accounts/ok', decoder_guard)
    add(version, 'unchecked decoder method remains unchecked', obj + '/try_from_unchecked/wrong_discriminator', decoder_method)
    add(version, 'exact discriminator error text', obj + '/try_accounts/wrong_discriminator', error_text)
    add(version, 'no decoder guard survives an error', obj + '/try_accounts/decoder_error', final_lease)
    add(version, 'error resources have the observed liveness', obj + '/try_accounts/decoder_error', error_lifetime)
    add(version, 'serializer partial effects survive its error', obj + '/exit/partial_write_then_error', data_not_written)
    add(version, 'serializer partial effects survive its unwind', obj + '/exit/write_then_unwind', data_not_written)
    add(version, 'serializer unwind releases its data guard', obj + '/exit/write_then_unwind', final_lease)
    add(version, 'serializer reports the actual copied prefix length', obj + '/exit/partial_write', write_count)
    add(version, 'memory copy receives the actual prefix bytes', obj + '/exit/write', memcpy_input)
    add(version, 'empty destination causes no memory syscall', obj + '/exit/empty_destination_has_no_memcpy', unexpected_memcpy)
    add(version, 'inner Accounts preserves exact bump mutation', 'boxed/try_accounts/inner_error_with_effects', bump)
    add(version, 'inner Accounts preserves realloc-set effects', 'boxed/try_accounts/inner_unwinds_with_effects', realloc)
    # The 0.27 driver records no Option APIs; these targets exist in the other corpora.
    if version != '0_27_0':
        add(version, 'optional inner error preserves bump effects', 'option/try_accounts/other_key_inner_error_with_effects', bump)
        add(version, 'optional inner unwind preserves realloc-set effects', 'option/try_accounts/other_key_inner_unwinds_with_effects', realloc)
    add(version, 'default exit has no syscall effects', 'default/exit/write', unexpected_memcpy)
    if version != '1_0_2':
        add(version, 'Owner precedes the decoder', 'account/try_accounts/ok', callback_order)
        add(version, 'close assigns the system owner', 'account/close/ok', closed_owner)
        add(version, 'close credit persists before source-write failure', 'account/close/source_write_conflict_after_credit', credited_lamports)
        add(version, 'close owner assignment survives resize failure', 'account/close/resize_conflict_after_transfers', closed_owner)
        add(version, 'close credit survives resize failure', 'account/close/resize_conflict_after_transfers', credited_lamports)
    if version in ('0_27_0', '0_32_1', '1_0_2'):
        add(version, 'Sysvar receives the original duplicate record', 'sysvar/try_accounts/duplicate_record', original_record)
    if version in ('0_27_0', '0_32_1'):
        add(version, 'owned Borsh String is dropped after replacement', 'sysvar/try_accounts/sysvar_borsh_error_is_dropped', owned_string)
        add(version, 'replacement installs even if old Drop unwinds', 'account/reload/old_drop_unwinds_replacement_installed', saved_payload)
    if version in ('0_32_1', '1_1_2'):
        add(version, 'InterfaceAccount releases data before old Drop', 'interface_account/reload/old_drop_unwinds_replacement_installed', callback_lease)


# Select original controls for the recorded cumulative library versions.
CONTROLS = [entry for entry in CONTROLS if entry[1] in ('anchor_lifecycle_0_27_0', 'anchor_lifecycle_0_29_0', 'anchor_lifecycle_0_32_1', 'anchor_lifecycle_1_0_2', 'anchor_lifecycle_1_1_2')]
