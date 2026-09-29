<!-- codex-design -->
# Full Pure-Simple SIMD Bootstrap: Detail Design

Status: Draft for implementation

Requirements: `doc/02_requirements/feature/full_pure_simple_simd_bootstrap.md`
and `doc/02_requirements/nfr/full_pure_simple_simd_bootstrap.md`.

This document defines the implementation contracts for the selected complete
fixed-and-scalable SIMD program. The architecture document owns layer placement
and bootstrap admission. This detail design fixes the callable interfaces,
database and HTTP integration, error behavior, fixtures, and Profile 2 evidence
needed by the implementation lanes.

## Shared types and dispatch

The platform-neutral library surface uses the shared names below. Callers do
not inspect CPU names, target triples, operating systems, registers, or vector
widths.

```simple
enum SimdBackend:
    Scalar
    Sse2
    Ssse3
    Sse41
    Avx
    Avx2
    Avx512
    Neon
    Sve
    Sve2
    Rvv
    Simd128

struct SimdCapabilities:
    backend: SimdBackend
    width_bits: i64
    feature_bits: u64
    os_state_ready: bool
    scalable: bool

struct SimdExecutionReceipt:
    selected_backend: SimdBackend
    width_bits: i64
    vector_chunks: i64
    scalar_tail_items: i64
    fallback_reason: text
```

`SimdLane<T, N>` supplies exact fixed-lane semantics. Scalable backends expose
the same operations through `ProcessingIR`; their backend chooses `vl` for each
iteration. `ProcessingIR` contains semantic operations rather than ISA names:
byte equality, delimiter/class masks, fixed-width comparisons, bitmap Boolean
operations, population count, and exact/reproducible numeric reductions.

Capability discovery runs once per process, validates every feature required by
the selected kernel, and publishes an immutable cached `SimdCapabilities`.
AVX-family selection includes CPU feature bits and required XCR0 state. SVE,
SVE2, and RVV selection includes usable runtime vector length. Wasm SIMD128 is
selected before loading a SIMD-requiring artifact. Concurrent readers never
repeat discovery. Test-only forcing creates a scoped dispatch instance; it does
not mutate the production cache or bypass capability validation.

Strict forced selection returns `Result<SimdDispatcher, SimdDispatchError>` when
the requested backend is unavailable. Automatic selection falls back to scalar
and records the reason. No path catches an unsupported-instruction fault and
continues.

## Database platform-neutral kernels

`DatabaseSimdKernels` is implemented under the shared pure-Simple library and
is consumed by `src/lib/nogc_sync_mut/db/accel.spl`. The database layer retains
its existing `ByteSpan`, `TextSpan`, `KeySpan`, `RowBitmap`, and predicate
interfaces. It does not import compiler backend modules, SFFI, `rt_*`, target
configuration, or operating-system modules.

Initial integrations are deliberately data-parallel and preserve the current
query plan:

| Existing operation | SIMD semantic operation | Required result |
| --- | --- | --- |
| `byte_span_equals`, `text_equals_span` | XOR/equality reduction | Exact Boolean equality |
| `byte_span_prefix_len`, delimiter scans | equality masks plus first-set-bit | Exact first differing/delimiter byte |
| `scan_text_values` equality predicates | batched byte compare and row mask | Same stable row bitmap |
| `scan_key_span` integer predicates | lane compare and mask pack | Same predicate and row order |
| `RowBitmap.and_with` / `or_with` | word-vector Boolean operations | Bit-exact bitmap including masked tail |
| `RowBitmap.count` | vector or scalar popcount | Exact count |
| `summary_text_hash` | widened partial sums with ordered final fold | Same modular hash |
| vector dot/L2 distance | reproducible reduction profile | Result within the selected FP contract |

`accel_capability_report()` reports the actual cached backend and sets
`simd_active` only when at least one database kernel is executable. Detection
alone never activates the DB path. Each operation chooses scalar for inputs
below its measured break-even size. Width selection occurs before the loop,
never once per row or chunk.

Fixed-width implementations process complete chunks followed by one bounded
scalar tail. SVE/SVE2 and RVV strip-mine with a fresh active-lane predicate for
each iteration. Loads remain within the declared span; neither implementation
reads past a buffer and masks afterward. Bitmap tails clear all bits beyond
`row_count`. Aliasing operations snapshot source lanes before writing when the
source and destination overlap.

PureDatabase remains the canonical engine. The SIMD work must not route through
`database/fast_db.spl` (`rt_db_*`) or the SQLite adapter. Existing file, socket,
and clock needs use the standard IO/capability owners. Direct file `rt_*`
declarations in legacy database modules are migration items for the portability
gate; SIMD code must not add or duplicate them. `PostgresMimicServer` continues
to compose `PureDatabase`; pgwire/network framing, when present, stays in a
transport adapter and never changes query semantics.

## Web-server platform-neutral kernels

`WebSimdKernels` is a pure-Simple semantic facade consumed by
`src/lib/common/net/http_core.spl`,
`src/lib/nogc_async_mut/http_server/parser.spl`, and the established HTTP
router/parser helpers. It has no socket, event-loop, TLS, file, thread, target,
or OS imports. IO remains owned by `IoDriver`, TCP/TLS/file/time facades, and
the existing capability routers.

The first integrations are:

| HTTP operation | SIMD semantic operation | Preserved behavior |
| --- | --- | --- |
| Find CRLF and header terminators | dual-byte delimiter scan | Exact earliest boundary across chunks |
| Classify request-line separators | byte equality/class masks | Existing method/path/version validation |
| Find header colon and trim OWS | delimiter/class scan | Case and whitespace rules unchanged |
| Case-insensitive known-header match | ASCII fold plus equality | Non-ASCII bytes remain scalar/rejected per current policy |
| Chunk-size/framing scan | CR/LF/hex classification | Existing malformed/oversize errors and limits |
| Route literal-prefix screening | prefix equality mask | Existing ordered route selection and parameter extraction |
| Response header/body copy | bounded vector copy | Byte-for-byte wire output |

The incremental parser preserves state across arbitrary feed boundaries. A
vector search may inspect only bytes already present in `buffer`; a delimiter
split across feeds is handled by retained scalar boundary state. Request-line,
header-count, header-line, encoded-body, and decoded-body limits are checked at
the same or earlier point as today. SIMD never converts malformed framing into
an incomplete request and never allows a larger allocation before rejection.

Routing keeps the existing registration-order winner. SIMD may reject literal
prefix mismatches in batches, but wildcard/parameter extraction and method
errors use the scalar semantic routine. Compression codecs are outside the
first integration unless a codec-specific correctness and performance fixture
proves the Profile 2 threshold. The content middleware registration stub is not
counted as SIMD implementation evidence.

`src/app/web/main.spl` must execute the admitted cached web artifact through the
production launcher contract. A per-request subprocess, raw-source execution,
or a hardcoded `./bin/simple` recursion is prohibited. Direct `thread_sffi`
imports in HTTP ownership modules must either move behind the existing task/
thread capability owner or be recorded as the already-authorized lower-runtime
boundary; DB/web leaf modules cannot depend on them.

## Module interactions

```text
DB Query / HTTP Parser
        |
        v
DatabaseSimdKernels / WebSimdKernels
        |
        v
ProcessingIR + cached SimdDispatcher
        |
        +--> scalar semantic oracle
        +--> fixed backend lowering (SSE..AVX-512, NEON, SIMD128)
        +--> scalable lowering (SVE/SVE2, RVV)
```

Callers pass spans, predicates, and destination buffers. The dispatcher returns
values plus an optional `SimdExecutionReceipt` when evidence mode is enabled.
Production hot paths keep evidence counters in bounded aggregates; they do not
format logs, scan the tree, read configuration, or shell out. Backend changes
invalidate only the test-scoped dispatcher. Database indexes and route tables
retain their current generation/invalidation rules because SIMD does not change
their keys, contents, or ordering.

## Correctness fixtures

One deterministic fixture generator supplies identical inputs to the scalar
oracle and every admitted backend. It produces lengths `0`, `1`, `lane-1`,
`lane`, `lane+1`, `2*lane-1`, `2*lane`, and `2*lane+1`, with start offsets from
zero through one lane minus one. Each operation includes all-equal data, first
and last-byte differences, missing and adjacent delimiters, repeated CR/LF,
high-bit bytes, embedded NUL, maximal/minimal integers, empty strings, duplicate
rows, all-zero/all-one bitmap tails, and overlapping input/output spans.

Database fixtures assert stable row IDs, bitmap bytes, counts, hashes, NULL and
type behavior, ordering, and unchanged serialized rows. HTTP fixtures fragment
each request at every meaningful boundary: inside CRLF, header name/value,
chunk-size line, chunk data, terminal chunk, and body. They assert the same
parsed request or typed error, consumed-byte count, retained buffer, limits,
route winner, response bytes, and connection decision.

Floating-point distance fixtures contain positive and negative zero,
subnormals, infinities, quiet NaNs, large cancellation, and non-multiple vector
lengths. Exact mode follows scalar operation order. Reproducible reduction mode
uses a documented fixed reduction tree and compares bit patterns except where
the requirement explicitly permits canonical NaN handling. Fast reassociation
is not used by database correctness paths.

Forced-backend negative fixtures remove one required capability at a time and
assert a typed strict-mode error before kernel entry. Automatic mode must return
the scalar value and a non-empty fallback reason. Native/QEMU rows record host
or emulator identity; an unavailable ISA stays BLOCKED with its exact resume
command and is not represented by a scalar pass bearing that ISA's name.

## Profile 2 benchmark design

Measurements run against the exact admitted Stage 4 candidate after one fixed
warmup phase. Every result records source revision, executable path and SHA-256,
host/VM identity, CPU features and OS-state readiness, selected backend, vector
width, fixture hash, warmup count, sample count, p50/p95/p99, throughput, maximum
RSS, scalar correctness hash, SIMD correctness hash, and pass/fail threshold.

Kernel microbenchmarks cover DB byte equality/delimiter scan, integer predicate
scan, bitmap AND/OR/count, modular hash, and HTTP CRLF/header classification.
The same process runs a forced scalar dispatcher and then the selected backend;
fixture construction and receipt formatting remain outside timed regions.
AVX-512 must reach 2x scalar throughput. AVX2, NEON, and SIMD128 must reach 1.5x
on their qualified rows.

The representative DB workload extends
`test/05_perf/bench/simple_db_shared_accel.spl`: a locked mixed select workload
over realistic rows exercises equality, range, multi-filter bitmap fusion, and
stable result materialization. The representative HTTP workload uses
`test/05_perf/web_server_nginx_compare/` and a native in-process parser fixture
with mixed request/header/body sizes. Each must improve throughput or elapsed
time by at least 20% against forced scalar, with identical correctness hashes.

The pre-change baseline and selected SIMD run use the same host, affinity,
candidate, fixture, warmup, and sample count. No supported backend may regress
p99. Compiler, MCP, DB, and HTTP profiles each enforce maximum RSS growth of
2%. Web comparison against nginx is retained as context; it does not replace
the required scalar-versus-SIMD comparison. A zero, missing, mismatched, or
unidentified measurement fails closed.

## Errors, fallback, and observability

Dispatch errors distinguish unavailable CPU feature, missing OS state, invalid
vector width, unsupported operation, invalid span, and strict backend mismatch.
Invalid spans and semantic input errors return the existing caller-visible
error and never fall back. Automatic fallback is allowed only for backend
availability, an operation not implemented by that backend, or an input below
the measured threshold. It must use the same scalar oracle and increment a
bounded reason counter.

Observable counters include discovery count, selected backend, per-kernel
vector chunks, scalar tail items, below-threshold fallbacks, unavailable-backend
fallbacks, and strict failures. They are read through a diagnostic snapshot;
request processing performs no per-call logging or allocation solely for
observability. Discovery count must remain one under concurrent DB and web use.

Any correctness mismatch disables promotion of that backend and fails the
verification row. Any meaningful performance regression is fixed within the
three-cycle cap or recorded as a concrete bug with owner, evidence, and exact
resume condition. A backend name, emitted opcode, or capability label without
executed correctness and timing evidence is insufficient.

## Test and evidence mapping

The executable system scenario uses the frozen helpers
`step_detect_simd_capabilities`, `step_run_scalar_oracle`,
`step_run_simd_backend`, `step_compare_database_results`,
`step_compare_web_results`, `step_bootstrap_platform_handoff_readiness`, and
`step_verify_deployed_tools`. Fixture/checker helpers are
`setup_simd_fixture`, `setup_database_fixture`, `setup_web_fixture`,
`check_simd_equivalence`, `check_simd_performance`,
`check_bootstrap_candidate`, and `check_deployed_simple_mcp`.

REQ-SIMD-001 through REQ-SIMD-004 map to capability, forced-negative, lane,
tail, mask, integer, FP, and alias fixtures. REQ-SIMD-005 through
REQ-SIMD-007 map to DB/HTTP equivalence, source dependency audits, and cached
artifact execution. REQ-SIMD-008 through REQ-SIMD-012 map to the Stage 1-4 and
tool phase matrix. REQ-SIMD-013 maps to artifact-presence and generated-manual
quality checks. REQ-SIMD-014 maps to the one-shot verification receipt and
linear sync evidence.

The mirrored manual presents capability detection, scalar/SIMD DB comparison,
scalar/SIMD HTTP comparison, bootstrap handoff, and deployed-tool verification
as the primary operator flow. Matrix mechanics remain folded. No helper may
return placeholder success; unfinished helpers fail explicitly.

## Implementation order

1. Land the scalar semantic operations and dispatcher contract.
2. Prove forced selection, feature/OS-state validation, cached discovery, and
   cross-width correctness before enabling any caller.
3. Implement fixed and scalable backends and admit them independently.
4. Integrate DB kernels through `db/accel.spl`; enable `simd_active` only for
   admitted operations.
5. Integrate HTTP classification and parsing with fragmented-input fixtures.
6. Run Profile 2 microbenchmarks, then DB and HTTP end-to-end measurements.
7. Bind results to the admitted Stage 4 candidate and deployment receipts.

The DB/web integration is complete only when callers remain platform-neutral,
all scalar-equivalence fixtures pass, Profile 2 thresholds pass on every
available qualified row, unavailable rows remain explicit, and final evidence
identifies the exact deployed binary.
