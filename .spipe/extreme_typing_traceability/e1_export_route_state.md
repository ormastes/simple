# E1 frozen export route observation slice

2026-11-03 base 0cf067f2871, after merged PR5960. User authorized implementation
and landing following independent structural review. Runtime remains unavailable.

Acceptance: actual retained registry supplied to the typecheck pass; fresh
signature records bound to canonical physical source/generation; frozen origin
and both declaration authorities agree; one callable observation joins to its
local ID, otherwise explicit Unknown; all work/retention bounded; absent and
stale generations cleared rather than reused. No enforcement or complete E1.

Owned source: common signature/export-route records; HIR route projector;
driver_hir_pipeline_passes, driver_hir_pipeline_lowering, driver_types,
driver_orchestration. Owned docs: detail design, infra guide, feature expert.
Luna alone authors api_export_route_projection_v1_spec.spl. design_review owns
independent source review. Prior E1 had two review/fix cycles; this slice starts
cycle 3 cumulatively. No repeated passing checks or Rust fallback.

Current: source and integration ready; specs/review pending. No runtime PASS,
manual generation, performance qualification, proof, commit or merge claimed.

Final source checkpoint: independent production-source and corrected six-case
spec review converged with zero unresolved findings. Tests use the real parser,
surface builder, HIR lowering and retained typecheck pass; direct/facade identity,
stale generation, absent registry clearing, duplicate observations, malformed
indexes and unfrozen registry are authored behavior checks, not executed proof.
One scoped tracked whitespace check passed. Parent already recorded working
environment guard PASS and doc/06_spec executable count zero; neither repeated.
Source frozen for parent commit/landing. Runtime and performance remain unrun.
