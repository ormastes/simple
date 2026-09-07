# Flat-AST bridge Phase 3 throughput blocker

**Status:** open design; no runtime ABI or Phase 3 candidate change is admitted.

## Symptom and scope

In the interpreted bootstrap lane, `flat_ast_to_module()` repeatedly reads the
legacy `SIMPLE_BOOTSTRAP_*` environment mirror through `rt_env_get` and
`rt_env_get_i64`. A feature-rich function has up to 24 syntactic declaration
getter calls; mode selection plus field fallback can turn those into roughly
100 Rust interpreter/SFFI crossings before statement, expression, and type
conversion. Since `getenv` scans an environment that grows with the flat AST,
the legacy path can become superlinear.

The compiled arena-preferred lane does not have this ownership problem and must
not be routed through a new snapshot format.

## Authoritative state and codec

The authoritative per-parse state is the Pure-Simple flat arena. Its only
complete serialized form is `spl-flatpool-v1`, produced by
`flat_pools_dump_all()` and consumed fail-closed by
`flat_pools_restore_all()` in
`src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl`.

The envelope contains seven fixed-order units:

1. declaration pools;
2. expression pools;
3. statement pools;
4. type pools;
5. parser state;
6. extend pools;
7. pending pools.

Completeness is guarded by `scripts/check/check-flat-ast-codec-complete.shs`;
byte fidelity is guarded by `scripts/check/check-flat-ast-roundtrip.shs`.
Neither gate may be weakened or replaced.

## Rejected narrow Rust provider

A Rust provider that scans `SIMPLE_BOOTSTRAP_*` keys and emits a new FAS/FAST
schema is unsafe and must not be implemented. The environment mirror is not an
authoritative copy of the seven units: type state and several declaration,
parser, extend, and pending pools are arena-only. Rust therefore cannot emit a
complete `spl-flatpool-v1` blob from the mirror without duplicating the
Pure-Simple codec and fabricating missing state. A missing field here is a
silent miscompile, not merely a cache miss.

`rt_env_all()` is also not a solution. It creates a rich aggregate containing
one allocation per key/value tuple, preserves the incomplete mirror, and adds
an aggregate ABI/ownership boundary to a path with prior aggregate-lifetime
failures.

No Rust AST-SFFI handle registry may be snapshotted: it is not the owner of the
Pure-Simple parse state.

## Candidate: bridge-scoped canonical arena mode

The smallest viable direction is entirely canonical:

1. Immediately after parsing and interpolation/desugar mutations finish, call
   `flat_pools_dump_all()` once while the authoritative arena is live.
2. Validate/restore that same `spl-flatpool-v1` blob through
   `flat_pools_restore_all()`; malformed, truncated, wrong-version, count, or
   trailing data remains a hard miss/failure, never an empty AST.
3. Enter a bridge-only arena-read mode for declaration, expression, and
   statement accessors, refresh their cached mode slots once, and run
   `flat_ast_to_module()` without per-getter environment reads.
4. Restore the previous mode in one exit path, including parser-error and panic
   cleanup. The blob and decoded temporary state are released exactly once.

This option is conditional on proving that all seven restored pool owners are
visible across interpreter module calls. If that proof fails, stop; do not
silently fall back field-by-field after admitting arena mode. The existing
legacy environment path remains the fallback before the bridge scope is
entered.

Cache invalidation is the existing arena contract: `ast_reset()` changes the
generation and clears the pools. A bridge snapshot records the generation and
module/decl counts at capture; entry rejects any mismatch, and mutation after
capture invalidates the scope. The transient snapshot is not persisted under a
second cache key or codec version.

## Runtime and ABI ownership

- **Pure Simple:** owns the seven pools, codec, generation/count validation,
  bridge scope, and the final `ParserModule`.
- **Interpreter:** may expose counters/timing for evidence, but must not own or
  reinterpret the blob.
- **JIT/native:** uses the same Pure-Simple codec and arena accessors; no noop or
  alternate provider is allowed.
- **core-C/bootstrap runtime:** needs no new provider for the preferred design.
  If a future design adds an extern, it must have a real `runtime.h` and
  core-C implementation, native-all provider, interpreter registration,
  `RUNTIME_SYMBOL_NAMES`/JIT signature, stage-4 symbol-closure evidence, and an
  ownership test proving its returned `RuntimeValue` is freed exactly once.

## Acceptance criteria

1. ParserModule output and diagnostics are identical between legacy and
   bridge-scoped arena modes for functions, extern functions, structs/classes,
   traits, enums with named/unnamed payloads, impls, imports/exports, type
   aliases, annotations, interpolation, extend state, and error parses.
2. `spl-flatpool-v1` completeness and whole-closure byte-roundtrip gates pass
   unchanged. Version mismatch, truncation, corrupt lengths, count/generation
   mismatch, and trailing bytes fail closed.
3. Instrumentation proves exactly one canonical dump/restore admission per
   parsed file and zero `rt_env_get*` calls from flat-AST getters while the
   arena bridge scope is active.
4. Median `flat_ast_to_module` throughput improves by at least **3x** on the
   legacy interpreted lane. The 400-to-1600-declaration normalized-time slope
   is at most 1.2x.
5. Peak RSS is bounded to input blob size plus decoded pools and is no more than
   1.15x the legacy peak on the representative fixture. Repeated-file runs show
   no monotonic retained-byte growth.
6. Arena-preferred interpreter, JIT, native, and core-C bootstrap behavior is
   unchanged; symbol and SFFI audits remain green.

## Focused verification and microbenchmark

- Add a representative Simple parity spec that parses once, records the legacy
  module/diagnostics, restores the canonical blob, runs bridge-scoped arena
  conversion, and compares all public module collections and diagnostic text.
- Extend codec tests with generation/count mismatch, post-capture mutation,
  wrong version, truncation, malformed length, and trailing-byte cases.
- Run `check-flat-ast-codec-complete.shs` and
  `check-flat-ast-roundtrip.shs` once each.
- Add an interpreter-only counter around `rt_env_get`/`rt_env_get_i64`, disabled
  by default, and assert no getter crossings inside the admitted scope.
- Generate fixtures with 100, 400, and 1600 functions, plus separate parameter
  and statement-body scaling fixtures. Warm once, measure ten conversions, and
  report median, p95, peak RSS, canonical blob bytes, getter crossings, and
  declarations/nodes per second.
- Run the same parity fixture through interpreter, JIT, native runtime, and the
  core-C bootstrap link/symbol check. Do not launch a full Phase 3 candidate
  until these focused gates pass.

## Stop conditions

Do not commit an implementation if semantic parity fails, the speedup is below
3x, memory exceeds the bound, any lane needs an incomplete/noop provider, or
the canonical codec gates regress. Preserve the current legacy path and record
the failing evidence instead.
