# Bootstrap Stage 4 AST/HIR overlap exhausts the no-GC heap registry

Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

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
failure. Stage 4 stopped before compilation with
`could not fingerprint Stage 4 source authority`. The initial source audit
found and removed the dead `src/app/spostgre` alias, but a later instrumented
authority walk showed that this was not the first failing record.

The run took 37m35s, peaked at 2,558,236 KiB RSS, and performed zero swaps.
Stage 2 SHA-256 was
`5f3a4a4eb948ffb2cb2f19b159d2b7b1d344879fa275da7d57bf313636f302af`;
Stage 3 SHA-256 was
`94d193374dd212f962bce4ef6b3c62516cd4bfee0d7b728c0d40754d76de8343`.
No Stage-4 candidate was admitted or deployed, so the NVMe post-bootstrap
SSpec/docgen gate was not run.

## 2026-07-28 owned tooling-source repair

The next bounded strict attempt again completed and sanity-checked Stage 2 and
Stage 3, then stopped at the same Stage-4 fingerprint boundary. It took
37m17s, peaked at 2,557,072 KiB RSS, and performed zero swaps. Stage 2 SHA-256
was `9ff6785f03cb81c08633b0e8d93fee8f8ace5dc83bb7fa6959879f135693c9b8`;
Stage 3 SHA-256 was
`f10afef864fc8f62226b83ff192ecdbc37a1601029638f7002d2f3c2a62dd8bc`.

An instrumented replay localized the first failure to `src/app/mcp_t32`, a
supported alias resolving inside the repository at
`examples/10_tooling/trace32_tools/t32_mcp`. The Stage-4 helper now treats
`examples/10_tooling` as owned source, hashes its files directly, permits only
canonical directory aliases into that tree or the existing `src/**` roots,
and prints the failing alias for unresolved or escaping links. The shared
Stage-3 snapshot also now emits the resolved-link records it validated; the
missing insertion had made its own symlink integration test fail.

The direct complete source-revision check now passes with SHA-256
`6286d44f93289b75e3b42e273083fcf71f026b2c1f645703181998be5f86302e`.
The Stage-3 source snapshot and jj-state portions of the portability gate pass;
that broader gate later stops on the unrelated retired-Windows-workflow check.
The one-attempt cap leaves Stage-4 compilation, deployment, and NVMe
post-bootstrap SSpec/docgen for the next bounded run.

## 2026-07-28 production Stage-4 gate wiring

The next strict attempt used the current Rust authority, completed and
sanity-checked Stage 2 and Stage 3, passed the repaired source fingerprint, and
entered Stage-4 compilation for the first time in this sequence. It took
31m42s, peaked at 2,923,264 KiB RSS, and performed zero swaps. Stage 2 SHA-256
was `d42064a6286128c0690bbafa4d0bcc6d04adc50f4935080db6b8851416becd4f`;
Stage 3 SHA-256 was
`17914479afe700d95fe37bc155861cf6ee7b19beb8aecc88844e1a59fb7b15d4`.

Stage 4 parsed 1,819 physical modules, then the legacy Phase-3 surface matcher
failed on alias `compiler.core.ast_stmt`. The production launcher set
`SIMPLE_BOOTSTRAP_STAGE4=1` but omitted the independent
`SIMPLE_STAGE4_STREAMING_SURFACES=1` admission flag, so the streaming ownership
implementation described above was never selected. The shared Stage-4 launch
function now sets that flag, and unit/system contracts plus the portability
gate require it. The one-attempt cap leaves compilation, deployment, and NVMe
post-bootstrap SSpec/docgen for the next bounded run.

## 2026-07-28 paired low-memory admission repair

The next bounded attempt again completed and sanity-checked Stage 2 and Stage
3, passed source attestation, and entered Stage 4. It took 31m54s, peaked at
2,923,468 KiB RSS, and performed zero swaps. Stage 2 SHA-256 was
`6f48099e3ac49299897bf2b71f95f8386b94be11899f6fc4428b9debdfe01d15`;
Stage 3 SHA-256 was
`fb9929d4e89c368966ea85565af83c773383595970dfd11f3efd05a62e28cba8`.

The log still took the legacy `phase2:parse:closure` branch and repeated the
`compiler.core.ast_stmt` alias failure. Source tracing localized the remaining
false predicate: `aot_native_project_with_backend_fixed` derives
`options.low_memory` from `SIMPLE_BOOTSTRAP_LOW_MEMORY`, while the streaming
selector requires both that option and `SIMPLE_STAGE4_STREAMING_SURFACES`.
The production launcher now sets both flags, matching the existing bounded
memory runner, and both unit/system contracts require the pair. The one-attempt
cap leaves Stage-4 compilation, deployment, and NVMe post-bootstrap SSpec/docgen
for the next bounded run.

## 2026-07-28 raw aggregate promotion repair

Retry 7 completed and sanity-checked Stage 2 and Stage 3, passed source
attestation, and selected the paired Stage-4 streaming/low-memory path. It
failed on the first physical source with `module surface promotion failed for
src/app/cli/main.spl`. The run took 29m43s, peaked at 1,643,920 KiB RSS, and
performed zero swaps. Stage 2 SHA-256 was
`b5389b154911bdab6c2a9ca5d7e62e12ee01e95f45eafdc335e297cef4ba8e5f`;
Stage 3 SHA-256 was
`697eda4ed6f86c22e6b98fb6bb8a32e378fd31d943f75fe766ea32c6815e428d`.

The failure was an ownership-graph representation mismatch. Native Simple
structs are raw `rt_alloc` word aggregates, but `rt_transient_heap_promote`
could traverse only tagged arrays, dictionaries, enums, floats, and closures.
The runtime now records raw allocations in a scope-local hash table and walks
their complete i64 words when they are reachable from a promoted root. The
walker marks reachable raw blocks persistent; scope end frees the remaining
parser-owned raw blocks and clears the metadata.
`HirLowering` itself is created before each parser scope, so it is not a valid
scope-owned root. Its redundant promotion was removed: lowering runs only
after the scope is paused, its newly allocated state is persistent, and the
retained `HirModule` root promotes shared parser-origin graph nodes.
The registered `lowering.errors` array is promoted separately so diagnostic
spans remain valid when the caller reports errors after scope end.
The focused core-C self-check passes through two nested raw carriers into the
existing cyclic array/dictionary/enum/closure graph. The deployed Simple test
runner could not execute the source contract because this worktree lacks its
`simple_seed` sibling and `std.spec` names did not resolve; that infrastructure
failure is not counted as Stage-4 evidence. The next bounded strict retry must
still prove live slope, deployment, and NVMe SSpec/docgen.

## 2026-07-28 Rust-provider parity repair

Retry 8 rebuilt current Rust authority, completed and sanity-checked Stage 2
and Stage 3, passed source attestation, and entered Stage 4. It again failed on
the first physical source with `module surface promotion failed for
src/app/cli/main.spl`. The run took 38m17s, peaked at 2,557,968 KiB RSS, and
performed zero swaps. Stage 2 SHA-256 was
`eedae92e756f12d93450355a411c61f35cc832f1c374404cbfe3fb395ee7e2c3`;
Stage 3 SHA-256 was
`7237281a2a0cd12a46f021f46e5c6eeb7077779290d45155cad546a0a0067a0a`.

GDB stopped at the actual Stage-3 `rt_transient_heap_promote` call and captured
argument `0x56d0b2f1`. Masking the tag produced readable `ModuleSurface`
storage at `0x56d0b2f0`, including source index zero, tagged path/name strings,
and content length 773. Disassembly then proved Stage 3 supplied the 46-byte
Rust promotion function while `rt_alloc` came from `runtime_memory.c`; the
core-C raw registry fixed after retry 7 was not this process's provider.

`runtime_memory.c` now tracks scope-owned raw allocations with native-width
words and exposes promotion/lifecycle hooks to the Rust runtime. Its allocation
and free signatures match the public ABI. The Rust graph walk treats scalar tag
collisions as leaves, handles tagged or untagged raw roots, heap-to-raw edges,
cycles, and repeated promotion, and scopes arrays, tuples, dictionaries,
objects, closures, enums, and boxed floats. The focused offline Rust test
`transient_heap_promotion_retains_reachable_cycle_only` passed on the third
bounded verification cycle; tuple/all-kind assertions were then added by
static review without a prohibited fourth rerun. A new strict bootstrap is
still required to rebuild Stage 2/3 with this parity fix and prove Stage-4 live
slope, deployment, and NVMe SSpec/docgen.

## 2026-07-28 declaration visibility recursion repair

Retry 9 rebuilt current Rust authority, completed and sanity-checked Stage 2
and Stage 3, passed the prior first-surface failure, and released 598 Stage-4
module surfaces before terminating with SIGSEGV. It took 44m06s, peaked at
2,559,008 KiB RSS, and performed zero swaps. Stage 2 SHA-256 was
`c5c0f8afb9dcac98c0e6a55dd0c71c4968043c90fa091cff00d84a51eecc0ef1`;
Stage 3 SHA-256 was
`6ae43d4a2c2770966357e764eabb68418a6f1f0bd28d9c5b50c6f29605eca0ed`.

An isolated GDB reproduction stopped in `getenv` after exhausting the stack.
The repeated caller was `decl_get_visibility_text`: its out-of-range legacy
fallback called `decl_get_is_pub`, which calls `decl_get_visibility_text`
again. There is no independent public flag; visibility is the authoritative
field and missing entries already default to private in arena mode. The
out-of-range legacy branch now returns `private` directly, with a focused
regression exercising a missing index while legacy storage is selected.

The same run emitted statement indices from earlier files against the current
small arena. Although the in-process native-build path attempts to enable
arena mode, Retry 9 proved the Stage-4 driver still reached legacy getters.
The production launcher and its live-slope gate now bind
`SIMPLE_NATIVE_ARENA_DECLS=1` before process initialization, disabling stale
declaration, statement, and expression environment mirrors for the entire
Stage-4 process. Both the production bootstrap and live-slope gate also reject
any residual out-of-range or missing flat-AST tag before admission, so the
bridge's legacy `NilLit` fallback cannot yield a deployed compiler. The
live-slope gate self-test and shell syntax checks pass.
The focused Simple spec is present but could not run because Stage3 rejects
the `test` command and the deployed CLI fails its bounded test-ABI probe;
using the Rust seed would violate bootstrap policy. Deployment and NVMe
SSpec/docgen remain pending the next bounded retry.

## 2026-07-28 Retry 10 module-global copy-out failure

Retry 10 rebuilt Rust authority, passed Stage 2/3 sanity and attestation, and
entered Stage 4 with `SIMPLE_NATIVE_ARENA_DECLS=1` present in the process
environment. It nevertheless reproduced the exact first stale statement IDs
at surface 375, eventually releasing 1,277 surfaces with 15,483 stale-tag
diagnostics. Phase 2 then returned with `ctx.module_surfaces` missing. The run
took 64m57s, peaked at 2,649,080 KiB RSS, and used zero swaps. Stage 2 SHA-256
was `3aa6334770a6ac18e3bc145990e6b27e5013da7f77caa5d4d67853e2220d3a77`;
Stage 3 SHA-256 was
`bd09bf6247475863d5ddddc47613de25554ba9b6c7c194b03dbbae8c128eda7b`.

The shared root was not the environment flag: Rust interpreter frame teardown
wrote callee-refreshed global overlays back as if the enclosing caller had
mutated them, clobbering newer AST counters, mode state, and retained compiler
context. `CowEnv` now distinguishes refreshed values from caller writes; all
mutation entry points clear that provenance, and owner-qualified updates cross
foreign-module frames without colliding by bare name. Focused scalar/write/array
and same-owner, `A -> B -> A`, plus ownerless-wrapper regressions pass, as does
the serialized 21-test module
global suite. Retry 11 must rebuild this Rust authority and prove the Stage-4
zero-diagnostic admission gate before deployment or NVMe SSpec/docgen.

## 2026-07-28 Retry 11 provenance fix insufficient

Retry 11 rebuilt commit `a7b53d603fc0` and passed Stage 2/3 sanity,
provenance, and native capability. Stage 4 still failed after 1,278 released
surfaces: the first OOB was `idx=6783` against `arena_len=101` immediately
after surface 374, followed by 10,292 OOB reads, 5,146 missing tags,
`n_modules=0`, and missing streaming surfaces. Wall time was 51m55s, peak RSS
2,650,944 KiB, swap zero. The provenance/owner-packet repair is therefore not
the complete root fix; Retry 12 is postponed until a focused regression proves
the remaining arena/context ownership or ordering defect.

The first focused repair after Retry 11 preserves defining-owner metadata for
imported global aliases. This directly covers the observed split reset:
`module_state.spl` imported declaration pools were previously discarded on
return while its owned statement arena reset persisted. An AST-shaped
two-module parallel-arena regression and the serialized 22-test module-global
suite pass. Entry publication, imported-alias refresh, and block/function
shadow relay regressions bring the serialized suite to 25/25. This is focused
evidence only; method/lambda lifecycle review and a
new bounded Retry 12 remain required for Stage 4 admission.

---

## 2026-08-17 (W2 driver lane) — FAMILY COLLAPSED; ROOT IS NOT IN 80.driver

These three rows were re-examined together as instructed, on the hypothesis that
one cause spans them (AST and HIR arenas live simultaneously):

- `bootstrap_stage4_selfhost_parse_memory_blowup_2026-07-20`
- `stage3_current_source_hir_rss_termination_2026-08-14`
- `bootstrap_stage4_ast_hir_overlap_memory_2026-07-27`

**The hypothesis is right, and the root cause is already written down in source,
with probe numbers — in `src/compiler/80.driver/driver_types.spl:1080-1100`:**

> The three evictions below drop references only. With no GC and no refcounting
> that reclaims NOTHING -- measured at 0 of 2001 allocations by
> `src/runtime/test/rt_driver_eviction_reclaim_selfcheck.c` (probe P0).
> ... Unblocking this needs class instances to be identifiable at runtime, a
> codegen/representation change, **NOT a driver change**.

So `evict_sources()` / `evict_ast()` / `evict_hir()` / `evict_mir()` are all
no-ops on the bootstrap lane, which is exactly why "clears the AST dictionary
after HIR" never reduced the peak, and why moving the eviction earlier in the
loop cannot help either. The overlap described in the 07-27 row is not a
sequencing defect in the driver; it is that nothing the driver can call frees
anything. The two obvious driver-level "fixes" were both already tried and both
measured HARMFUL: `rt_dict_free_deep` frees key strings aliased from outside the
dict by HIR/AST/SymbolTable (use-after-free, probes P2/P3), and per-module
lowerer reconstruction is the retained-aggregate boundary the 08-14 row fixed.

### Verdict per row
- **08-14** — source fix CONFIRMED PRESENT and now guarded by a spec (single
  lowerer hoisted out of the loop, one reused diagnostics buffer, no
  surface/trait copies through per-iteration locals). Executable RSS evidence
  still requires one canonical Stage-3 transaction; not run (a user bootstrap
  was live and `build/bootstrap/**` was off-limits).
- **07-20 / 07-27** — **BLOCKED-CROSS-OWNER.** The remaining fix is a runtime
  representation change so that a class instance carries a tag/header the heap
  registry can identify, in `src/runtime/runtime_native.c` (heap registry /
  `rt_alloc` class-instance representation) plus the native class-layout emitter.
  Those files are outside the 80.driver ownership boundary, so nothing was
  edited there. No driver-side change can close these two rows.

### What was NOT measured, stated plainly
No RSS number was produced for the pure-Simple lane in this session. The only
figure obtained was **3,050,124 KiB peak RSS** (`/usr/bin/time -v`) for the
**Rust seed** `bin/release/x86_64-unknown-linux-gnu/simple` interpreting
`src/compiler/80.driver/main.spl --check <one tiny file>` — a different memory
model entirely, and therefore evidence for nothing on these rows. It is recorded
only so it is not mistaken later for a lane measurement. Per the 08-14 row's own
warning: on this host a status-143 exit is indistinguishable from an earlyoom or
watchdog kill, so **143 without a monotonic RSS trace is not a reproduction.**

### Family guard
`test/01_unit/compiler/driver/driver_memory_lifecycle_family_spec.spl` —
`Results: 5 total, 5 passed, 0 failed`. It fails if a deep-free call is
reintroduced into the driver context, if the measured hazard rationale is
deleted, or if the HIR loop goes back to constructing a lowerer per source.
