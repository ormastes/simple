# Bootstrap Stage 4 AST/HIR overlap exhausts the no-GC heap registry

## Status

Open. The full `src/app/cli/main.spl` Stage 4 closure still does not produce a
native executable on the 4 GiB-class Linux development host.

## Reproduction

Run the Stage 3 compiler with `SIMPLE_BOOTSTRAP_STAGE4=1`,
`SIMPLE_NO_STUB_FALLBACK=1`, `--entry-closure`, `--low-memory`, one thread, and
the `src/compiler`, `src/app`, `src/lib`, and `examples/10_tooling` source roots.
The closure contains about 1,303 unique modules.

Evidence is retained under:

- `build/mini_builds/stage4_retry21.log`
- `build/native_probe/stage4_retry21.time`

## Observed

- Original peak RSS: about 6.1 GiB, terminated by OOM.
- After closure/cache and frontend-memory fixes: about 3.0–3.7 GiB.
- After reusing one pre-registered HIR diagnostic buffer: 2,812,760 KiB.
- The remaining failure is `runtime error: field access on nil receiver` after
  the terminal `future.spl` HIR module returns and before diagnostic collection
  completes.
- Earlier phase tracing measured about 21.85 million registered heap objects at
  the terminal HIR module.

## Root cause

The low-memory pipeline releases raw source contents after parsing and clears
the AST dictionary after HIR, but peak memory occurs during HIR. At that point
all parsed `Module` ASTs, accumulated `HirModule` values, and the flat bootstrap
HIR store are live together. The core-C bootstrap runtime has no tracing GC;
most dictionaries, enums, closures, strings, and conversion-created arrays
remain allocated/registered after Simple references are dropped.

The C array registry also ignores registry-growth allocation failure and can
return an unregistered heap handle. That is a correctness bug, but correcting
it alone only turns the memory failure into an explicit allocation failure.

## Implemented mitigation

The driver now allocates one typed `[LoweringError]` buffer before the HIR loop,
passes it into a dedicated `HirLowering` factory, projects diagnostics through
owner methods, and clears/reuses the same registered handle. This reduced the
measured peak by roughly 300–800 MiB without changing diagnostics.

The diagnostic projection is now flat and span-free (`[text]` plus `[bool]`),
avoiding the bootstrap ABI failure when a nested `Span` is extracted from an
array-held `LoweringError`. Stage 4 subsequently completed HIR collection
instead of trapping on the terminal `future.spl` module.

Phase 2 retains all logical aliases in `modules_by_name`, but now passes only
its unique physical source list into Phase 3. On the full CLI closure this
removed 420 duplicate HIR lowerings (1723 aliases versus 1303 files), reduced
diagnostics from 6132 to 5206, and reduced peak RSS from 4,059,988 KiB to
3,493,940 KiB.

HIR glob registration now expands one hop through declaration-empty facade
modules and resolves their explicit export lists. The bounded version reduced
the next diagnostic set from 5206 to 2315 and eliminated the dominant
`MirType`/`MirTypeKind` family. An earlier unrestricted depth-8 expansion is
rejected evidence: it was killed at 6,169,364 KiB. The bounded run completed
Phase 3 diagnostic collection at 4,352,600 KiB.

Subsequent source-accurate fixes added the omitted MIR operand re-exports,
completed the lexer scanner's selective helper import, accepted `me` as an
alias of the canonical `self` HIR receiver, exported split parser AST types,
and corrected MIR optimization imports. Diagnostics fell from 2315 to 1212
with a 3,769,480 KiB peak, then to 722 with a 4,291,316 KiB peak. The remaining
largest families are explicit re-export/type-alias facades (`T32BridgeResult`,
`FixConfidence`, `Replacement`, `EasyFix`) rather than the original memory or
nested-diagnostic crash.

## 2026-07-28 eager imported-trait amplifier

A fresh isolated Stage 4 run exposed a later regression before browser
verification could start: after 215 HIR modules it held about 203 million heap
registry entries and 35 GiB RSS. Small re-export/sibling modules with zero or a
few local functions added 11-26 million entries while resolving imports.

The flat-function accumulator was initially suspected but falsified: it resets
for every bootstrap module, live per-module counts are local, and core-C array
pushes retain shallow handles. The dominant avoidable work is eager lowering of
every imported trait default. That lowering is needed only when the importing
module has an impl of the trait.

The source repair records imported parser traits and lowers a trait on demand
when `lower_impl` needs its defaults. Focused unit scenarios cover glob and
named/aliased imports: unused traits stay unlowered, while imported traits used
by an impl retain their defaults and first-binding collision semantics. The
stale pure-Simple runner cannot execute the scenario; the
explicit Rust diagnostic runner reached a pre-existing `Unknown type:
ParseError` frontend failure, so no PASS or memory reduction is claimed yet.
The unchanged-source Stage 4 build terminated without a candidate at about 97
GiB RSS and 543 million heap registry entries. A first glob-only repair build
was stopped at 101 million entries when review found named imports still took
the same eager path; no memory reduction is claimed from that incomplete run.

A cache-isolated Stage 3 diagnostic then lowered the repaired current-source
`bootstrap_main` closure and emitted 695-709 objects without HIR/type failure.
Both bounded attempts stopped at link on symbols outside the selected minimal
core-C runtime lane, so they prove source/object emission only, not a runnable
or admissible compiler.

Three full-CLI verification cycles then isolated the remaining owner. The
glob-only and all-import trait deferrals both reached about 203 million native
registry entries at HIR module 215/216, matching the unfixed run. A final
one-thread run with `SIMPLE_BOOTSTRAP_LOW_MEMORY=1` and per-expression phase
tracing disabled followed the same slope and was stopped at the mandatory
cycle cap after 64 minutes and about 80 GiB RSS, without a candidate.

The core-C bootstrap registry has no reachability collector: it retains native
arrays plus immortal strings, dicts, enums, and closures. Low-memory mode can
drop raw source after parsing and AST/HIR/MIR only at whole-phase boundaries,
but Stage 4 still holds every parsed `Module` while accumulating every
`HirModule`. Import/package-sibling registration adds fanout, but the measured
dominant bug is this whole-phase AST/HIR lifetime overlap. No safe per-module
registry reset exists because it would also invalidate retained modules.

One safe duplicate owner was removed before the next full measurement: Stage4
normal MIR lowering reads `ctx.hir_modules`, but HIR finalization also copied
every module's symbols, functions, constants, enums, structs, and classes into
the bootstrap flat-HIR globals used only by the non-Stage4 bootstrap MIR path.
Stage4 now skips both materializing and retaining that parallel aggregate;
non-Stage4 entry-closure behavior is unchanged. This is a bounded retention
repair, not yet evidence that the remaining whole-phase peak fits the host.

The next retained-log audit found that the earlier "physical" source dedup was
still lexical: `_driver_unique_physical_sources` normalized `.` and `..` but did
not resolve repository symlinks. The same file therefore still entered Phase 3
through aliases such as `src/lib/...` and `src/std/...`; one measured
`nogc_async_mut/io.spl` duplicate added about 15.6 million registry entries.
The shared source key now drives closure-scan membership, parse dedup, and alias
cache lookup through `rt_path_absolute` (realpath on POSIX, platform-canonical
absolute paths elsewhere) with lexical normalization as the final fallback. A focused regression
pins both the `src/std -> src/lib` and `src/compiler/frontend -> 10.frontend`
aliases. This removes proven duplicate lowering; it does not claim to solve the
necessary whole-phase AST/HIR lifetime.

## 2026-07-28 focused compiler admission

Building `src/app/cli/native_build_worker.spl` instead of the full CLI bounded
the same compiler capability at 446 MiB peak RSS and 5m56s. The first artifact
was rejected because permissive bootstrap linking generated a `panic` stub.
With `SIMPLE_NO_STUB_FALLBACK=1`, a 300-second per-file limit completed all
source objects at 899 MiB peak, then failed closed at the provider boundary:
the core-C bootstrap archive lacks hosted compiler hooks and several legacy
runtime helpers. The source-matched `libsimple_compiler_backfill.a` owns the
Cranelift hooks; the fresh core-C runtime owns `panic`; remaining legacy owners
must be supplied through the existing validated external-provider link boundary
without enabling stubs. The three-cycle cap stopped further build retries.

## 2026-07-28 phase-profiler amplification

An exact Stage4 full-CLI run with phase profiling produced 52,584 verbose HIR
messages while lowering only 50 modules and reached 11,986,204 KiB max RSS in
9m00s before it was stopped. The HIR diagnostic gates incorrectly treated
`SIMPLE_COMPILER_PHASE_PROFILE=1` as a request for per-expression and
per-function tracing. Those verbose allocations are now restricted to
`SIMPLE_COMPILER_TRACE=1` or `SIMPLE_BOOTSTRAP_DIAG=1`; phase profiling keeps
only bounded phase events.

A comparison run with phase profiling absent produced no verbose output, but
still reached 7,374,600 KiB RSS at 5m46s. The logging fix removes avoidable I/O
and no-GC allocations, but does not change the primary whole-phase AST/HIR
retention diagnosis below.

The first strict pure-Simple `native_build_worker` was admitted through an
exact 13-root runtime projection and then used to compile the hosted browser
entry closure. Its RSS reached 48,167,848 KiB in 6m20s before the run was
stopped. The equivalent current Rust-seed worker stayed near 2.1 GiB RSS but
remained CPU-bound without producing an artifact after 45 minutes. This proves
the production blocker is the self-hosted compiler's retained allocation
growth, not the browser renderer or the runtime-provider link boundary.

## Required structural fix

Introduce a two-pass, streaming HIR pipeline using `ModuleSurface` as compact
cross-module authority:

1. Parse/extract imports, signatures, composites, enums, constants, traits,
   impl signatures, aliases, and required trait default bodies.
2. Reparse or retain one module body at a time.
3. Lower it against module surfaces.
4. Publish its flat-HIR record and release its AST/body before advancing.

Tests must cover glob imports, aliases, imported enum variants, trait defaults,
impl signatures, deterministic closure order, and entry-closure output parity.

## Acceptance

- Full Stage 4/4b/5 bootstrap completes on the target PC.
- Peak RSS remains below the host limit with `SIMPLE_NO_STUB_FALLBACK=1`.
- The deployed `bin/simple` builds and runs a representative program.
- No generic/diagnostic errors are suppressed to obtain the binary.

## 2026-07-28 experimental ownership implementation

The structural path now exists behind the additional
`SIMPLE_STAGE4_STREAMING_SURFACES=1` admission gate. Phase 2 parses one physical
source in a transient heap scope, pauses allocation, builds and promotes only
its compact `ModuleSurface`, then clears parser roots and reclaims the rich
module. Phase 3 reparses one source at a time, lowers HIR while allocation is
paused, promotes parser-owned values reachable from the HIR root and lowering
diagnostic/cache state, and then reclaims that source's AST. Type aliases, enum
variants, trait defaults, impl signatures, and source aliases remain in the
cross-module surface.

The core-C runtime now scopes arrays, dicts, enums, closures, and boxed floats;
strings remain persistent. All tracked heap kinds share the existing
open-addressing pointer registry, so membership and scope-end reclamation do
not scan cumulative arrays or persistent strings. Recursive promotion is
cycle-safe and serialized against unregister/free. The ASan+UBSan ownership
selfcheck passes cyclic reclamation/promotion and bounded scope-end checks
after 100,000 persistent strings and 20,000 persistent arrays.

This is implemented but not admitted. The available pure-Simple binary parsed
the changed driver successfully, then its repository-wide hygiene subprocess
failed on unrelated concurrent work. Its stale test runner could not resolve
`std.spec`. A fresh Stage 4 compiler and the required live registry/RSS slope
remain the next evidence; none of the acceptance items above is marked complete
from static contracts or the C selfcheck alone.

## 2026-07-28 bootstrap runtime parity repair

The first source-current strict full-bootstrap attempt reached Stage 2 and
failed at link time because `module_surface_promote` requested
`rt_transient_heap_promote`, while the Rust bootstrap runtime exported only the
transient scope begin/pause/end functions. The C production runtime already
implemented recursive promotion. The attempt took 22m56s, peaked at
2,558,872 KiB RSS, performed zero swaps, and retained the failed objects under
`build/bootstrap/stage3/x86_64-unknown-linux-gnu/native-objects-FDWaEJ`.

The Rust bootstrap runtime now implements the same reachable-graph operation
for its array-only transient ownership scope. Traversal is cycle-safe across
arrays, tuples, dictionaries, objects, closures, and enums; scope end reclaims
only arrays unreachable from the promoted root. The focused offline unit gate
passed:

```sh
env CARGO_BUILD_JOBS=1 cargo test --locked --offline \
  --manifest-path src/compiler_rust/Cargo.toml -p simple-runtime \
  transient_heap_promotion_retains_reachable_cycle_only -- --nocapture
```

This closes the Stage-2 symbol divergence only. Stage-4 admission, live slope,
deployment, and production SSpec/docgen remain pending the final strict retry.

## 2026-07-28 final strict retry

The third and final strict retry rebuilt the Rust authority, completed and
sanity-checked both pure-Simple Stage 2 and self-hosted Stage 3, and therefore
confirmed the transient-promotion runtime repair through the prior link
failure. Stage 4 stopped before compilation because the fail-closed source
fingerprint found `src/app/spostgre` dangling to
`../../examples/spostgre/src/tool` and reported
`could not fingerprint Stage 4 source authority`.

The run took 37m35s, peaked at 2,558,236 KiB RSS, and performed zero swaps.
Stage 2 SHA-256 was
`5f3a4a4eb948ffb2cb2f19b159d2b7b1d344879fa275da7d57bf313636f302af`;
Stage 3 SHA-256 was
`94d193374dd212f962bce4ef6b3c62516cd4bfee0d7b728c0d40754d76de8343`.
No Stage-4 candidate was admitted or deployed, so the NVMe post-bootstrap
SSpec/docgen gate was not run. The next bounded session must repair or remove
the dangling source link before one new strict bootstrap attempt.
