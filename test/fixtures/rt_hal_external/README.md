# RT/HAL external comparator fixtures

These test-only C and Rust executables implement the fixed
`rthal-scalar-v2` comparison protocol. Pure Simple remains the semantic and
effect owner. Each child independently derives outcome and query-trace digests
from the operation/input words using the documented fixed SplitMix64 transform;
it does not echo the expected Pure outcome. Replay additionally consumes the
already-observed Pure trace but never repeats the host effect. The matching
Pure reference is `rt_hal_external_expected_receipt` in `fixture_plan.spl`, so
any C/Rust/reference divergence is falsifiable.

`setup_and_compare.spl` requires canonical absolute compiler paths, their
64-digit SHA-256 identities, the canonical repository root, and absolute output
paths. The output directory must already exist. It compiles both fixtures only
through `EnvAccessPlan.RunAllowedTool` as static non-PIE ELF executables, admits
each result through the runtime's ELF descriptor gate, pins each executable by
a fresh SHA-256 identity, installs that provider plan, and runs two exact cases.
Dynamic ELF, static PIE, or a toolchain without complete static closure returns
a typed `RTHAL-FIXTURE-BLOCKED-v1` scenario receipt instead of substituting a
dynamic fixture.

Required arguments:

- `--repo=<canonical-absolute-root>`
- `--cc=<canonical-regular-file>` and `--cc-sha256=<64hex>`
- `--rustc=<canonical-regular-file>` and `--rustc-sha256=<64hex>`
- `--c-output=<absolute-path>` and `--rust-output=<absolute-path>`

The provider ABI is mode-specific and oracle-free. Query receives exactly 12
arguments after `argv[0]`: schema, mode, case ID, effect flag, then operation
and input digests (four signed 64-bit decimal words each). Replay receives four
additional trace words as effect input. Neither mode receives Pure expected
outcome or error data, and query receives no Pure trace. Success emits exactly
`RTHAL1 <outcome-4> <error-4> <trace-4>` and a newline. Malformed input exits
nonzero without a receipt. The parent admits a receipt only after parsing it
and authoritatively reaping the child with exit status zero; EOF alone fails.

The same executables also expose the bounded `rthal-io-v2` fixture mode. Its
stdin frame is exactly
`RTHAL2 <request-byte-length> <effect-byte-length>\n<request-hex><effect-hex>`;
lengths count decoded bytes and hex is lowercase. Compare requires a zero
effect length. Replay requires an effect frame containing little-endian u32
payload and event-byte lengths followed by those two spans. The pinned parent
owns exact frame production; children consume exactly the declared spans and
do not wait for EOF on the still-open pipe. Header whitespace, uppercase hex,
overflow, inconsistent lengths, invalid candidates, and malformed transcripts
fail closed. Each decoded span and result is capped at 1 MiB and held in fixed
buffers.

The request is the little-endian `HIO2` v2 envelope: case/request/schema IDs,
five valid type candidates with canonical descriptor bytes, explicit operation
and input codec transcripts, and declared output/error/effect encodings. The
legacy scalar fixture requests require output type and encoding to equal input,
copy the input value, and retag its root transcript from Input to Output. Error
and query Effect are canonical three-event Unit transcripts; replay validates
and retains the supplied Effect transcript without executing the effect again.

Success writes exactly `RTHAL2 <result-byte-length>\n<result-hex>`. The decoded
result begins `RTHIOV2\0`, uses signed little-endian i64 scalars, carries zero
as the untrusted provider-ordinal sentinel, repeats all five foreign candidates
and descriptors, and supplies Output/Error/Effect transcript streams. The
parent substitutes its owner-issued ordinal, atomically readmits identities,
and reconstructs values only after complete framing and exit-zero validation.

`rthal-io-v2` is retained only as a quarantined legacy fixture protocol.  Its
old codec-reframing behavior is not semantic parity and must never be selected
for a typed `@rt(hal, c|rust)` comparison.

Typed query providers use `rthal-io-v3 compare <operation-id> <adapter>`.
The startup plan binds exactly one nonempty, NUL-free UTF-8 operation identity
(at most 4096 bytes) and one bounded native adapter.  HIO2 V2 is the complete
request: its Operation stream is that exact identity, and its Input candidate,
canonical tuple transcript, and payload are the typed parameters.  No
`RTHEXIT2`, Pure outcome, Pure error, Pure effect, pointer, object image, or
expected receipt is accepted by V3.
V3 replay is explicitly unsupported unless a separately registered native
effect adapter exists; it never reuses a Pure effect trace as a result seed.

Adapter `4` is the separately registered V3 idempotent EnvAccess `record`
effect adapter. It is usable only with `rthal-io-v3 replay <operation-id> 4`.
The paired replay frame is exactly `u32 payload_len, u32 event_len, payload,
events`; payload is `RTHALENV3` (9 ASCII bytes), little-endian version `3`,
opcode `1` (`record`), little-endian argument length, then those argument
bytes. Events must be the four canonical Effect-domain `bytes` events. The
native adapter validates the complete plan, records the case/schema pair once,
and only then constructs a fresh canonical effect receipt. Unknown operation,
non-idempotent opcode, malformed length/events, or a conflicting record fails
closed with exit `78`; V2 is never used for replay.

The `record` argument is an exact bounded EnvAccessPlan image: LE body version
`1`; length-prefixed UTF-8 plan ID and canonical repository root; LE total-byte
and process budgets; counted tool `(id,path,sha256)` and probe
`(id,schema,args,timeout,stdout,stderr)` allowlists; then counted instructions
`(kind 1..24, resource, arguments, timeout, stdout, stderr)`. Both providers
consume the image exactly and validate the same plan, path, hash, duplicate,
resource, allowance, per-probe, aggregate-byte, and process-cap constraints
before recording. The envelope is not accepted as an opaque byte echo.

The fixture registry has three independently implemented, allocation-free
query adapters: `1` copies a one-`bytes` tuple, `2` folds a one-`bytes` tuple to
`u64`, and `3` reverses a one-ASCII-`text` tuple. Adapter `4` is reserved for
a separately registered effect replay implementation and is rejected by the
query path. Each requires its exact
input/output/error/effect descriptors and canonical event sequence, then emits
its own `RTHIOV2` Output/Error/Effect streams.  A registry miss, operation-ID
mismatch, malformed parameter transcript, unsupported non-ASCII text, or
descriptor mismatch fails closed with `RTHAL-PROVIDER-E-UNKNOWN-OP` (exit 78)
or a malformed-frame exit; no identity/prefix fallback exists.  Production
plans must register an exact source-file-plus-function operation ID and an
independently maintained native implementation before controller sealing.
V3 startup admits adapters `1`–`3` only for `compare`, and adapter `4` only
for `replay`; other mode/adapter pairs are rejected before stdin is read.
