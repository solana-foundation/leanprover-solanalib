"""Semantic changes that the exact utility reference checks must reject."""
from common import on_record, outside_precondition


def set_path(path, value):
    def mutate(record):
        target = record
        for component in path[:-1]:
            target = target[component]
        target[path[-1]] = value
    return mutate


def uninitialized(record):
    record['state']['syscalls']['replies'][0]['data'] = ''


CONTROLS = [
    ('rent: exact comparison', 'utility_modern3', on_record('exempt/default/890880', set_path(['outcome','result'], False))),
    ('rent: NaN cast', 'utility_split222', on_record('exempt/qnan/0', set_path(['outcome','result'], False))),
    ('legacy rent: overflow is before comparison', 'utility_legacy115', on_record('exempt/add_overflow/18446744073709551615', set_path(['outcome','reason'], 'attempt to multiply with overflow'))),
    ('epoch: first boundary', 'utility_modern3', on_record('solana_epoch_schedule::EpochSchedule::get_first_slot_in_epoch/0/14', set_path(['outcome','result'], 524257))),
    ('epoch: final saturating subtraction', 'utility_legacy115', on_record('solana_program::epoch_schedule::EpochSchedule::get_last_slot_in_epoch/2/18446744073709551615', set_path(['outcome','result'], 18446744073709551615))),
    ('legacy115 sysvar: builtin cutoff', 'utility_legacy115', on_record('rent/builtin22', set_path(['outcome','result','err'], 'InvalidAccountOwner'))),
    ('legacy118 sysvar: string payload', 'utility_legacy118', on_record('clock/builtin15', set_path(['outcome','result','err'], 'BorshIoError("Changed")'))),
    ('split sysvar: status is not folded', 'utility_split222', on_record('clock/status1', set_path(['outcome','result','err'], 'UnsupportedSysvar'))),
    ('split sysvar: default tail survives', 'utility_split230', on_record('rent/ok/rate_only', set_path(['outcome','result','ok','burn_percent'], 0))),
    ('epoch getter: padding offsets', 'utility_modern3', on_record('epoch_get/ok/no_bytes', set_path(['outcome','result','ok','first_normal_slot'], 0))),
    ('hash: zeroed buffer persists', 'utility_split222', on_record('hash/0/unchanged_error', set_path(['outcome','result'], '01' * 32))),
    ('hash: partial tail stays zero', 'utility_legacy118', on_record('hash/0/one_byte', set_path(['outcome','result'], 'ff' * 32))),
    ('hash: singleton empty slice', 'utility_modern3', on_record('hash/0/full', set_path(['outcome','state','syscalls','log',0,'fields'], []))),
    ('hash: every return initializes', 'utility_modern3', outside_precondition('hash/0/nonzero', uninitialized), 'EveryReturnInitialized does not hold'),
    ('compute log: exact request', 'utility_legacy115', on_record('compute', set_path(['outcome','state','syscalls','log',0,'syscall'], 'sol_get_epoch_schedule_sysvar'))),
    ('log: embedded UTF-8', 'utility_split222', on_record('log/3', set_path(['outcome','state','syscalls','log',0,'bytes'], '00'))),
    ('current index: footer value', 'utility_instructions3', on_record('current/4/0', set_path(['outcome','result','ok'], 1))),
    ('current index: checked subtraction panic', 'utility_instructions4', on_record('current/0/0', set_path(['outcome','reason'], 'range start index exceeds slice length'))),
    ('current index: release shared guard', 'utility_instructions3', on_record('current/4/0', set_path(['outcome','state','write_ok'], False))),
    ('current index: wrong ID precedes busy borrow', 'utility_instructions4', on_record('current_wrong/4', set_path(['outcome','result','err'], 'AccountBorrowFailed'))),
    ('instruction: parse errors remain InvalidArgument', 'utility_instructions3', on_record('truncated/3', set_path(['outcome','result','err'], 'InvalidInstructionData'))),
    ('instruction: parsed accounts dropped on Err', 'utility_instructions4', on_record('truncated/6', set_path(['outcome','state','frees'], []))),
    ('instruction: high flag bits ignored', 'utility_instructions3', on_record('instruction/1/0', set_path(['outcome','result','ok','accounts',4,'is_signer'], False))),
    ('instruction: returned allocation stays live', 'utility_instructions4', on_record('instruction/2/0', set_path(['outcome','state','live'], []))),
    ('instruction: retained owned data', 'utility_instructions3', on_record('instruction/2/0', set_path(['outcome','result','ok','data'], '000100'))),
    ('instruction: exact capacity', 'utility_instructions4', on_record('instruction/1/0', set_path(['outcome','result','ok','account_capacity'], 4))),
    ('legacy getter: owned String is allocated', 'utility_legacy118', on_record('clock/builtin15', set_path(['outcome','state','strings'], []))),
    ('legacy getter: allocation remains live', 'utility_legacy115', on_record('rent/builtin15', set_path(['outcome','state','strings',0,'live'], False))),
    ('legacy getter: actual String capacity', 'utility_split222', on_record('rent/builtin15', set_path(['outcome','state','strings',0,'capacity'], 0))),
    ('legacy getter: actual String contents', 'utility_split230', on_record('clock/builtin15', set_path(['outcome','state','strings',0,'text'], 'Changed'))),
    ('legacy getter: String is fresh', 'utility_legacy118', on_record('rent/builtin15', set_path(['outcome','state','strings',0,'fresh'], False))),
    ('split hash: partial tail stays zero', 'utility_split222', on_record('hash/0/one_byte', set_path(['outcome','result'], 'ff' * 32))),
    ('split hash: empty input is one slice', 'utility_split222', on_record('hash/0/full', set_path(['outcome','state','syscalls','log',0,'fields'], []))),
    ('selected getter: allocation stays live', 'utility_split230', on_record('clock/builtin15', set_path(['outcome','state','strings',0,'live'], False))),
    ('selected getter: capacity holds the literal', 'utility_split230', on_record('rent/builtin15', set_path(['outcome','state','strings',0,'capacity'], 0))),
    ('selected getter: String is fresh', 'utility_split230', on_record('rent/builtin15', set_path(['outcome','state','strings',0,'fresh'], False))),
]


# Select original controls for the recorded cumulative library versions.
CONTROLS = [entry for entry in CONTROLS if entry[1] in ('utility_instructions3', 'utility_instructions4', 'utility_legacy115', 'utility_legacy118', 'utility_modern3', 'utility_split222', 'utility_split230')]
