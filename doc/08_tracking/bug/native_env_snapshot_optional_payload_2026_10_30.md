# Checked environment snapshots retain an unintended Option payload

Status: typed library boundary repaired; focused native regression PASS.
Private-daemon/SSpec acceptance and broader verification remain pending.

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
an empty text value distinct from a missing pair.

## Focused native validation

Compiler SHA-256:
`5dd85ea67087e063ae3a68ad0b282c82443e2ade6a178e0f10187fa93028260c`.
The immutable 80-path consumer source manifest has SHA-256
`da6c7966a4c578d0a4c710eb67728d21e7bfed161a98a7167864e865be77be58`.
It starts from generation-3 base `86b39` and includes repair
`bb0b52de8dcecee229168710502470cacf6cca51`. Its async module preserves the
upstream shared `env_vars_nilable` adapter and adds this explicit-match repair;
that integration was independently source-reviewed. This is a consumer build
with the admitted generation-2 compiler, not a new producer qualification.

Receipts:
`D:/dev/simple-runner-env-consumer-evidence-20261030/regression-env-snapshot-02`.
The 61-module build and executable both exited 0. Stdout is exactly
`ENV_SNAPSHOT_OPTIONAL_PAYLOAD_PASS`. Executable SHA-256:
`6e376650af80af39d5b12901a7ed3becd2e0285722caec923b3c393a62e4bff0`.
Build peak RSS was 4085408 KiB; run peak RSS was 2544 KiB. Both process-tree
receipts report quiescence.

Attempt `regression-env-snapshot-01` stopped with resource exit 88 at a 4 GiB
cap. Attempt 02 continued its compatible cache with an 8 GiB cap; the earlier
resource failure is retained and is not a passing test result.

This qualifies the focused sync/async snapshot, `?` consumer, and intentional
optional payload controls. It does not establish private-daemon startup,
SSpec execution, or broad compiler/library acceptance. Runner acceptance with
the next admitted producer remains pending.
