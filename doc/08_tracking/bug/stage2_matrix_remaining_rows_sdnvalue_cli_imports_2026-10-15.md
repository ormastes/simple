# Site 19: stage2-compiler-tests remaining rows on release_phase3 a1d66e52 (2026-10-15)

## Status: OPEN — two failing rows block stage2 full admission; cascades block three more

Measured on `release_phase3` tip `a1d66e52206` with the canonical macOS
stage1→2 bootstrap (llvm/dynload, jobs=2, 8 GiB RSS cap, full MC/DC waiver
atoms). Stage1 seed build, stage2 native compile (1348 modules), LINK,
sanity probes, and the struct-receiver proof ALL PASS — including with the
original single-line `else: return false` source (PR #3484 seed fix
verified at bootstrap scale; zero `unresolved call 'return'` warnings). All
8 `_cg` module-compile rows now PASS (previously failing).

The slim-profile matrix then fails these rows:

## Row 1: `test_runner_build` (FAIL)

From
`stage2-compiler-tests/.../verification/logs/test_runner_build.log`
(compiled by the STAGE2 pure-Simple compiler, not the Rust seed):

```
[ERROR] MIR lowering error: enum construction 'lib.common.sdn.value.SdnValue::Array':
        payload type mismatch at 0 at src/lib/common/sdn/value.spl:54:9
[ERROR] MIR lowering error: B5b: match has multiple wildcard arms
        (arm 1 in fn lib.common.sdn.value.SdnValue.is_null, module lib.common.sdn.value)
error: in-process native-build: MIR lowering error: enum construction
       'lib.common.sdn.value.SdnValue::Array': payload type mismatch at 0
```

`src/lib/common/sdn/value.spl` is clean at the source level: the enum
declares `Array([SdnValue])`, the constructor receives `items: [SdnValue]`,
and `is_null` has exactly one wildcard arm. Both errors are stage2
lowering artifacts in the test-runner closure (the build also covers
`lib.nogc_sync_mut.test_runner.test_db` and
`app.test_runner_new.sdn_worker_protocol`).

Related advisory storm in the same row family:
`[hir-payload-origin-unresolved] owner=lib.common.sdn.value payload=Dict:
no declaration, re-export hop, or explicit import of this name in the
owner`. `Dict` is a builtin container and is deliberately NOT filtered by
`hir_dependency_is_builtin_type` (user modules may declare `Dict`; see the
docstring in `20.hir/hir_lowering/_Items/module_reexport_materialization.spl:1647`).
In a small two-module closure this advisory is benign (compile phases
succeed); in the test-runner closure it likely becomes load-bearing through
cross-module type-identity divergence — establish that link before
changing either side.

## Row 2: `compiler_cli_build` (FAIL)

From `.../verification/logs/compiler_cli_build.log` (~34 MB, ends in):

```
error: in-process native-build: HIR lowering error in
       src/compiler/70.backend/backend/backend_types.spl: unresolved type: BackendKind
error: in-process native-build: HIR lowering error in
       src/compiler/25.traits/associated_types.spl:129:26: unresolved name: Span
error: in-process native-build: HIR lowering error in
       src/os/drivers/pci/pci.spl: unresolved name: _pci_ecam_base at :0:0
```

Diagnosis per residual:

- `Span` (associated_types.spl:129): genuine missing explicit import —
  only reachable via the `compiler.frontend.core.lexer.*` glob, which the
  materialization walk excludes. Fixed in this branch by the same
  documented pattern as trait_def.spl/trait_impl.spl
  (`use compiler.common.diagnostics.span.{Span}`).
- `BackendKind`: declared in the SAME file (backend_types.spl:22), so the
  error position is fabricated — the walk reports against an importing
  module, not the owner. Needs owner-walk diagnosis against the full-CLI
  closure to find which importer cannot name BackendKind and what route
  (export hop / named import) it lacks.
- `_pci_ecam_base` (pci.spl, inside `@cfg(arm64)`/`@cfg(riscv64)` blocks):
  called but declared NOWHERE in the tree — a genuinely lost helper. The
  provider model carries the platform value as `PciHostConfig.ecam_base`
  (pci_provider.spl:25), so the missing shim likely returned the boot
  host's configured ECAM base. Needs the SimpleOS PCI driver owner;
  inventing a hardcoded base would be a semantic guess.

## Cascaded rows (not independent defects)

`stage2_tool_workers` FAIL (worker-failed cascade), and
`compiler_bootstrap_tests` / `interpreter_interpreter_tests` /
`loader_interpreter_tests` UNSUPPORTED (`full-cli-artifact-not-built`)
— all three unblock once Row 2's CLI artifact builds.

## Repro notes

- Rust-seed minimal repros of the SdnValue enum shape (multi-variant,
  recursive payloads, static constructors, `is_null` wildcard) do NOT
  reproduce: the defect is stage2-only and closure-dependent.
- Ad-hoc stage2 invocations die earlier at
  `provider-artifact-not-mach-o` in Darwin link-provider admission
  (runtime/provider env of the matrix campaign is required), so row-level
  reproduction should go through
  `scripts/bootstrap/bootstrap-from-scratch.sh --stop-after-stage2` with
  the four `SIMPLE_MCDC_OFF_WAIVER_*` atoms, not hand-rolled native-build.

## Suggested order

1. `Span`/`BackendKind` import-owner residuals (Row 2) — same fix pattern
   as the landed hir_definitions named-import family; unblocks four rows.
2. SdnValue MIR payload identity (Row 1) — needs the advisory-to-error
   chain established in the test-runner closure first.

## Tooling note (found while landing this record)

`check-no-conflict-markers-push.shs` fails closed with "changed 1 path(s) but
0 were scanned (1 deletion(s))" on a deletion-only commit, blocking an
otherwise clean push. A deletion cannot introduce a conflict marker; the
gate should PASS on ranges whose only changes are deletions. Left as a
recorded defect for the hook owner rather than bypassed with --no-verify.

## Addendum 2026-10-15: second stage2-only codegen defect in the same closure

Reproducing the test_runner_build row outside the campaign env
(same admitted stage2 binary, same entry/sources/threads) dies EARLIER
than the campaign's SdnValue MIR error, at an LLVM codegen ICE in the
same module family:

```
error: unsupported LLVM value conversion from void to i64
       function=lib.nogc_sync_mut.test_runner.runner_lifecycle.cleanup_and_exit
error: 2 module(s) failed with ICE:
       lib.nogc_sync_mut.test_runner.runner_lifecycle (codegen, caught),
       lib.nogc_sync_mut.test_runner.test_runner_mcdc_formal_context (codegen, caught)
```

The retained llc diagnostic (build/native_cache/s98b3bcc*/simple-aot-
diagnostic-*/message) shows the true failure is a missing ptr->i64
conversion in a DEAD block emitted after the function's `ret`:

```
define i64 @...runner_mcdc_eval_program_cached(ptr %l1, ptr %l2, ptr %l3):
  ...
  ret i64 %l32
bb2:                                  ; unreachable, still emitted
  %l28 = getelementptr ptr, ptr %l3, i64 %l1   ; %l1 is ptr — needs ptrtoint
```

The live block correctly emits `ptrtoint ptr %l1 to i64` before use; the
post-ret block bb2 uses the ptr parameter directly as the GEP index.
Seed compiles this module fine (stage2 native compile passed) — the
defect is stage2 MIR->LLVM only. Likely the same bb2-emission path feeds
the `cleanup_and_exit` void->i64 poisoning. Reaching the campaign's
SdnValue MIR error requires the campaign's exact env (unreconciled:
sharded-frontend policy alone did not suffice), so row-level work should
fix or suppress the dead-block emission path first — it may unblock the
build to the point where the SdnValue error becomes directly reachable.

## Addendum 2026-10-16: SdnValue trigger bisected (three 5-minute closure runs)

Hypothesis-tested by editing only the enum's Dict variant in
src/lib/common/sdn/value.spl and re-running the exact test_runner_build
row entry against the GEP-fixed stage2 compiler:

| Enum Dict-variant shape | `SdnValue::Array` payload mismatch? |
| --- | --- |
| `Dict(Dict<text, SdnValue>)` (authored) | YES (plus fabricated B5b wildcard) |
| `Dict(Dict<text, i64>)` (builtin container, no recursion) | NO |
| `DictPlaceholder(i64)` (plain payload) | NO |

Trigger: a recursive enum reference routed THROUGH a builtin generic
container payload (`Dict<text, SdnValue>`). Direct recursion
(`Array([SdnValue])`) is fine; the builtin container alone is fine; the
combination breaks stage2 MIR payload validation, and the failure is
REPORTED against the sibling Array construction (value.spl:54), so the
enum's whole registration identity is poisoned, not just the Dict slot.
Consistent with the `[hir-payload-origin-unresolved] payload=Dict`
advisory seam: the cross-module materialization walk cannot name a
declaring module for builtin containers, and the recursive element inside
that unresolved payload never canonicalizes to the enum's own symbol.

Fix direction: canonicalize builtin-container payload ELEMENT types to
the declaring enum's recursive symbol during enum payload registration
(module_lowering.spl:900-946) or in the alias comparison
(enum_constructor_payload.spl:216), so an unresolvable container hop no
longer poisons sibling payload slots. Fast iteration harness: exact row
entry (test_runner_new/main.spl, 265-module closure) with
--cache-dir per experiment, ~5 min per run; the separately recorded
runner_lifecycle void->i64 ICE remains after the GEP fix and is its own
defect in the same module family.

## Addendum 2026-10-16 (late): owner-canonicalization fix measured; B5b root cause read from the code

PR #3488 (fold enum payload owner spellings through
mir_layout_canonical_module_name in enum_payload_named_alias_equal) was
verified in a full stage1->2 campaign: the `SdnValue::Array` payload type
mismatch is GONE. The B5b error REMAINS, and reading expr_dispatch.spl:6594-6615
shows exactly why: `is_null` has one wildcard arm (`case _:`); B5b fires only
when an arm DEGRADES to wildcard. `case Null:` degrades when the enum variant
`Null` is not found in the lowering's variant registry — the same two-spelling
identity split, one consumer over: the enum's variant/discriminant registry
lookup by bare name misses for the re-materialized enum, so the arm falls back
to wildcard and collides with `case _:`.

Remaining fix: make the enum variant registry (enum_variant_index_q /
enum_variant_discriminant registration in module_lowering.spl) canonicalize
the enum owner the same way — register/look up variants under the folded
dotted module name so a re-materialized enum declaration resolves by the same
key its match arms use. The bisection table and the construction-side fix
evidence above carry over unchanged.

## Addendum 2026-10-16 (final): B5b degrades in the frontend bridge, not MIR

Combined campaign (owner-canonicalization + metadata-owner + both backend
fixes): `payload type mismatch` count is ZERO — the construction side is
fixed. B5b persists. Reading expr_dispatch.spl:6490-6541: MIR's wildcard
duplicate check fires only when the FIRST arm is already a Wildcard kind.
`case Null:` must therefore arrive at MIR as Wildcard — it is degraded in
the frontend FlatAstBridge (convert_nodes.spl:1593-1652, the documented
"B5b shard-registry family" site), which cannot resolve the enum-variant
name against the subject type at bridge time in this closure. The
metadata-owner fix (enum_constructor_metadata_owner) stays: it hardens a
genuinely wrong ambiguity call for the constructor path, but it is not the
B5b consumer. Remaining fix belongs in the FlatAstBridge enum-subject
resolution (one identity layer above the two MIR fixes already landed).

## Addendum 2026-10-16 (third layer): B5b replays from the mono archive

Ruled out, with evidence: (a) the FlatAstPattern catch-all degradation
fired only for tags 33 (EXPR_UNIT, 21x), 26 (EXPR_LAMBDA, 17x), 13
(EXPR_ARRAY_LIT, 4x) across the closure — never EXPR_IDENT, so
`case Null:` was not dropped at the bridge; (b) MIR's reclassification
failure path keeps the arm a Binding (expr_dispatch.spl:6562), and the
scalar gate tolerates Binding+Wildcard without B5b. The only remaining
route for arm 0 to BE a Wildcard at the scalar gate is that the arms were
READ AS Wildcard from materialized state: the mono archive captures
module bodies in ArchiveRequests mode while the enum subject is
unresolved (the same unresolvable `Dict<text, SdnValue>` seam), degrading
`case Null:` at capture time; every later lowering replays the poisoned
archive body. Fix direction: make enum variant names resolve during
archive body capture (the ensure_archive_nominal_table_v2 /
MonoTemplateBodyModeV1.ArchiveRequests path in 40.mono), so archived
bodies retain Enum patterns for their own module's variants.

## Severity note (2026-10-16)

src/lib/common/sdn/value.spl alone has ~15 bare-variant match arms
(`case Null:`, `case Bool(_):`, ...) across is_null/is_bool/is_number/
as_bool/as_int/... plus 19 `case _:` arms. If enum-subject resolution
fails for the module the way is_null evidences, EVERY one of those matches
degrades; B5b trips only on the first `variant + case _` pair and is the
fail-closed tripwire — without it the module would compile to silently
wrong predicates. Treat the archive-capture fix as correctness-critical,
not a single-function anomaly. The serialized parser-v4 HIR cache
(*.parser-v4.hir under the row cache dir) holds the post-bridge arms and
is the fastest place to confirm the degraded shape once a decoder lands.

## Minimization probes (2026-10-16)

With the GEP/void/owner fixes in the stage2 compiler, neither
`--entry src/lib/common/sdn/strict_v1.spl` (the enum's main consumer, compile
phases clean; only the ad-hoc harness link-provider limitation fires) nor
`--entry src/lib/nogc_sync_mut/test_runner/test_db.spl` reproduces B5b or
the payload mismatch. Only the full
`--entry src/app/test_runner_new/main.spl` 265-module closure reproduces.
The mono-archive capture context that degrades the arms therefore
activates at whole-entry scale, not at consumer-module scale — debugging
needs the full closure or an archive-body dump, both owned by the mono
lane's infrastructure.

## Fifth layer (2026-10-16): the registry itself is absent in replay

PR #3493 (unique-owner fallback also when the subject route misses) was
campaign-verified: B5b PERSISTS. The fallback is never reached because
`variant_owner_keys("Null")` does not yield exactly one owner in the
archive-replay lowering instance — the MIR enum variant registry
(enum_variant_index_q) is never populated for modules whose bodies are
lowered from the mono archive in ArchiveRequests mode; the registry is
built only when a MirLowerer instance processes the enum's HirEnum
declaration, which body-only replay does not do. Fix direction (mono
archive owner): at the replay/lowering boundary, register the replayed
module's enum variants into the MIR registry from the archive nominal
rows (mono_archive_nominal_*), or re-lower the enum declarations
alongside the bodies. The scalar-gate message "multiple wildcard arms"
for is_null was emitted from the WILDCARD branch: arm 0 (`case Null:`)
is an unresolved Binding that consumed the default slot, arm 1 (`case _:`)
then collided — the text names the wrong arm kind (diagnostic polish,
separate).

## Stage3 frontier (2026-10-17): mono passes; MIR enum-construction registration divergence

With the mono fix (#3588) and the 20 GiB ceiling (#3589), stage3 on macOS
builds past the mono phase (peak 13.9 GiB, status=complete) and fails in MIR
lowering:

```
MIR lowering error: enum construction: missing runtime identity for 'Option'
MIR lowering error: enum construction: unregistered declaration
  'compiler.common.driver_core_modes.CompileMode'
  at src/app/cli/bootstrap_main.spl:380:20 and :550:20
```

SEED-WORKS / STAGE2-FAILS DIVERGENCE: stage2's own build compiled the same
entry (bootstrap_main.spl) with the same construction sites successfully —
stage2 was built by the Rust seed; stage3 is built by the stage2 (pure-Simple)
compiler. The self-hosted compiler does not register what the seed registers
for enum constructions reached through mono-specialized/generic contexts
(Option's runtime identity; a qualified enum key from an imported module at
the entry's construction sites).

Checked and ruled out: register_module_enum_inventory_v1 (#3527) and the
provider-enum paths DO call register_enum_variants, which registers runtime
ids — so the gap is in which modules/instantiations those passes cover in the
stage3 schedule, or in mono's minted instantiations needing their own runtime
registration (#3521/#3526 family). Owner: self-host divergence lane.
Repro: the stage3 resume command in /tmp/resume34-cap12.sh (final-push
worktree); HIR is cached so the mono/MIR phases re-run in ~15 min.

## Module-emission divergence (2026-10-17): whole modules absent from stage3 objects

After #3595 (stage3 bootstrap enum inventory), stage3's mono and MIR phases
PASS and the final link fails: `app.cli.bootstrap_focused_native_build.
run_exact_stage3_focused_capsule` / `run_exact_stage4_focused_capsule` and all
of `bootstrap_focused_native_build_args` are referenced (U) from
bootstrap_main.o but DEFINED NOWHERE in the stage3 object set (nm across all
native-objects-*/0-*.o: zero focused_* definitions, no mono renames). The seed
emits these modules (stage2's own build, same entry, linked fine); the
self-hosted stage2 compiler's module scheduler skips BOTH modules entirely
despite phase1 closure scans, imports, and direct uses in the entry's normal
paths (cache_dir at bootstrap_main.spl:413 etc.).

WORKAROUND (uncommitted, final-push verification tree only): the three
flag-readers bootstrap_main needs are inlined into bootstrap_main.spl (entry
module, which the scheduler always emits), and the two focused-capsule
dispatch routes return a clear error. This unblocks the stage3 link; the
focused-capsule sub-build routes are disabled in the self-hosted binary.

Owner: self-host divergence lane. The scheduler skips exactly these two
modules — the trigger (naming? import shape? demand propagation through
`use ...{a, b, c}` explicit lists?) needs the seed-vs-stage2 scheduler
comparison; the repro is the stage3 resume in /tmp/resume34-cap12.sh
(HIR cached, mono/MIR/link re-run in ~20 min).

## Emission divergence is systemic (2026-10-17, second stage3 link)

The focused_native_build workaround cleared its two symbols; the next stage3
link fails on 25 undefined symbols across ~17 modules, including function-
level gaps in core modules (`lib.nogc_sync_mut.io_runtime.env_get`,
`dir_create` — not whole-module) and driver modules (`compiler_driver_create`,
`run_native_build_entry_v1`, K1 backend table, compile-options/result helpers).
Counting evidence: the stage3 link inputs carry ~44 defined symbols across 40
fresh objects; the remaining module objects must come from the content-keyed
native cache, and the missing 25 are functions whose emitting modules produced
no object in this scope. Stage2's build (by the seed) emitted all of them.

This is NOT module-pair-specific: the stage2-built compiler's emission/cache
diverges from the seed's across the closure. Inlining is not viable at this
scope. Owner: self-host divergence lane — the seed's emitter/caching is the
reference; compare emission+native-cache admission for the 25 named symbols
(repro: /tmp/fullchain-monofix.sh on the final-push tree; HIR cached, link
verdict in ~20 min).
