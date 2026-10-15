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
