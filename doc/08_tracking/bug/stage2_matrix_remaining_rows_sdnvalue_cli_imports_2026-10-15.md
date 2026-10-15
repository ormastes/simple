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
