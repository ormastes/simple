# Stage 2 omits split impl providers from the native entry closure

Date: 2026-08-22
Status: PARTIAL — Phase 2 admitted; focused specs and Stage 3 pending
Owner: compiler module closure / split impl registration
Severity: P0 for current ARM64 bootstrap and SimpleOS QEMU rendering

## Exact failure

After restoring `PatternKind.TypeTest`, a strict ARM64 trust-root Phase 2
compiled the full closure and failed at link with six undefined method symbols:

- `HirLowering.union_narrow_arms`, defined only in
  `_Expressions/union_narrow_arms.spl`;
- `MethodResolver.fill_call_defaults`, `resolve_call_args`,
  `resolve_call_result_type_raw`, `resolve_comp_clause`, and
  `resolve_verification_contract`, defined only in
  `35.semantics/resolve_lookup_helpers.spl`.

Both provider files extend a type declared by their caller module, but no live
module imported the provider. Native entry-closure discovery therefore had no
edge that could retain either object. The fix explicitly imports each split
impl provider from its owning caller module, matching the existing compiler
driver split-impl registration pattern.

## Evidence required

1. Fresh strict Phase 2 links and passes its sanity and struct-receiver gates.
2. The union-narrowing and generated-visitor specs remain green.
3. Stage 3 no longer reports these six undefined symbols.

No seed fallback, weak symbol, fabricated stub, or whole-tree inclusion is an
acceptable substitute for the explicit owner-to-provider closure edges.

## Current evidence

The third guarded cycle produced and admitted Phase 2 SHA-256
`2090f5506fc5ba218d3526f3ae49f121b16e97a04b70a4c9ec1674a5773a315b`;
the six undefined method symbols are absent from the canonical link, and both
admission gates pass. A standalone full-compiler regression build is still
blocked by 16 separately owned unresolved runtime symbols, so criteria 2 and 3
remain open and this record is not resolved.

Revalidated 2026-11-02: still plausible because doc Status is PARTIAL (Phase 2 admitted; focused specs and Stage 3 pending).

## Update 2026-11-02 (lane p0f-2)

Fix confirmed present in source (commit 567e35070c9 "fix(bootstrap): retain
split impl providers in stage2"): the explicit provider imports are
`src/compiler/20.hir/hir_lowering/_Expressions/match_desugaring.spl:23`
(`union_narrow_arms`) and `src/compiler/35.semantics/resolve.spl:26`
(`resolve_lookup_helpers`). Focused spec added:
`test/01_unit/app/cli/entry_closure_split_impl_spec.spl` (3/3 pass; fails 2/3 with the two edges removed; fixture
`test/fixtures/entry_closure_split_impl/`) pins the two real import edges; `entry_closure_split_impl_walk_spec.spl` asserts the walker
`_native_build_entry_closure` includes a split impl provider only when the
type owner imports it (walker spec UNVERIFIED: the installed runtime timed out at 898 s loading the driver).
Stage 3 verification (criterion 3) remains pending.

## Update 2026-11-03: instance 2 (CompilerDriver.stage_lower_hir)

`driver_unit_tldr_imports_v1.spl` called `driver.stage_lower_hir("check")`
(split impl in `driver_orchestration.spl`) importing only the type owner
`driver_compiler_type`; frozen stage2 MIR lowering: "unresolved method call
'stage_lower_hir' is a FATAL lowering error". Importing `driver_orchestration.*`
widens the closure into `driver_aot_pipeline -> plugins.backend_vhdl`.

Fix: new narrow provider `src/compiler/80.driver/driver_stage_hir_v1.spl`
(`stage_lower_hir_run_v1` / `_failure_v1` / `_done_v1` / `_check_v1`,
`build_trace_first_error`), imports limited to the type owner,
`driver_hir_pipeline_lowering` (closure scanned: 623 files, no aot /
orchestration / vhdl), log helpers. `driver_orchestration.stage_lower_hir`
delegates to it and keeps only aot go-to-end recovery. The TLDR caller imports
the provider and calls `stage_lower_hir_check_v1()`.

Sibling found: `cache/driver_hir_source_body_surfaces_v1.spl` calls
`driver.add_streaming_module_surface` (defined in
`driver_source_parse_selected.spl`) without importing it; edge added. The
other non-impl caller, `driver_source_llvm_ir.spl`, imports
`compiler.driver.driver` (full driver), so its closure already covers the
providers.

Release-side workaround (tagged `@workaround bug=stage2_split_impl_...`):
the TLDR unit HIR step returns the fail-closed gap
`stage-lower-hir-gap:split-impl-provider-unverified` unless
`SIMPLE_UNIT_TLDR_STAGE_HIR=1`. Nothing consumes that result.

Spec: `test/01_unit/app/cli/stage_hir_split_impl_provider_spec.spl` (6/6 pass;
5/5 failed before the fix) + fixture `test/fixtures/stage_hir_split_impl/`.

Verification pending (needs stage3): build phase 3 from this source with
`SIMPLE_UNIT_TLDR_STAGE_HIR=1`; expect no "unresolved method call
'stage_lower_hir'" / `add_streaming_module_surface` and no
PRECLOSED_ALIAS_IMPORT_MISSING for backend_vhdl; then delete the workaround.
Open class: no static guard yet maps every `driver.X(` call to an imported
provider; `self.X(` calls inside split impls are not scanned.
