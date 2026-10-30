# Checked environment snapshots retain an unintended Option payload

Status: native failure proven; typed library boundary repaired, native regression pending.

Generation-2 compiler `5dd85ea67087e063ae3a68ad0b282c82443e2ade6a178e0f10187fa93028260c`
built standalone runner `e54464152e94c60610f18d15af71f4709c5ff54fd3acf94704d97c640c8ea0dd`.
The runner failed private-daemon acknowledgement before executing the SSpec body.
Its child reached readiness and returned status 2. Nonce and executable digest
comparisons passed; only the environment digest comparison failed.

The child digest `67cbe48c87c312fe186fd29cd3c5305ebbaae9c555b728caa2c771683c322cbd`
is exactly SHA-256 of `native-session-profile-v3` followed by one newline:
the daemon hashed zero environment rows. The parent copied zero inherited rows
and appended only its three private identity variables. Those three variables
arrived unchanged in the child's actual Windows environment.

LLDB stopped the actual runner at each returning boundary:

- `rt_env_vars`: `Array(len=122)`.
- `env_vars_nilable`: `Some(Array(len=122))`.
- `env_list_checked`: `Ok(Some(Array(len=122)))`.

The last return violates the declared `Result<[(text, text)], text>` contract.
Both configured `env_list_checked` implementations used a nil guard followed
by `Ok(values)` while `values` still had Optional storage. Both emitted the
saved Option directly into `rt_enum_new(0, 0, payload)`. Array consumers then
saw an Option object instead of an array and observed length zero.

Retained evidence:
`D:/dev/simple-runner-generation2-evidence-20261030/env-boundary-01/lldb.log`,
`env-snapshot-disassembly.log`, `env-checked-async-disassembly.log`, and
`handshake-env-03/lldb.log`. Environment diagnostics record names and value
hashes, not plaintext values. The frozen producer and runner sources were not changed.

The library repair explicitly matches `Some(values)` before constructing
`Ok(values)` in both sync and async variants. `None` keeps the allocation-failure
Err; `Some([])` remains a successful empty snapshot. The daemon's identity
checks and environment contract are unchanged.

Compiler gap remains open: the native pipeline admits the short nil-guard form
without rejecting the Optional-to-array mismatch or materializing a proven
narrowing conversion. This change does not claim general nil-guard flow typing.
A compiler repair needs explicit dominance/type evidence and must preserve
intentional `Result<Option<T>, E>` payloads.

`test/fixtures/compiler/native_env_snapshot_optional_payload.spl` exercises the
real sync and async snapshot APIs with a process-local sentinel, the `?` consumer,
and intentional None/Some(empty)/Some(nonempty) Result payload controls, including
an empty text value distinct from a missing pair. The fixture has not yet run
with this repair; private-daemon and SSpec acceptance remain pending.
