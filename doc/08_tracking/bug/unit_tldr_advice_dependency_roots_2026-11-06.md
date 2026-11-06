# Unit TLDR planning omitted advice dependency roots

Status: source repair prepared; native baseline blocked by non-public parser statics; full producer verification pending.

The root qualification attempt retained under
`/home/yoon/dev/simple-bootstrap-qualification-20261106/build/bootstrap-qualification/`
failed with `FILE-WORKER-E-CLOSURE-INCOMPLETE: aop advice outside import closure`.
The advice classifier had independent false positives, repaired in a separate
owner. Even genuine advice has a second problem: the PM3 plan walked imports
only from `mir_targets`, while parsing advice through a later extra-path flag.
An advice module could therefore have an unbuilt dependency surface.

## Requirement and repair

REQ-AP-01: a picked target and a genuine advice root must have their dependency
surfaces available to the existing readiness consumer. REQ-AP-02: advice roots
do not become picked targets, and existing four-argument plan calls retain
scope and behavior.

`driver_unit_tldr_plan_v1.spl` owns the staging-independent planner; the old
`driver_unit_tldr_imports_v1.spl` facade reexports its public API and retains
CompilerDriver lowering. `unit_tldr_plan_v1` now accepts an optional advice-path list. It parses the
union of picked and deduplicated advice roots and traverses their import
frontier through the existing summary/fallback machinery. The streaming
caller supplies `mir_advice_paths`. Returned `plan.picked`, per-unit claims,
MIR output ownership, readiness refusal and AOP weaving gates are unchanged.
This does not load every inventory module.

## Focused regression and limitations

The fixture at `test/fixtures/bootstrap/unit_advice_plan/` contains target a,
genuine advice z, z importing h, h importing q, and unrelated u. The regression
uses the production import-edge scanner and surface-readiness consumer against
real planner parse/surface availability. It also checks picked ownership,
duplicate advice roots, unrelated-module exclusion and the old API default.

## Retained attempts and next proof

Attempt 1: `/home/yoon/dev/simple-bootstrap-advice-plan-20261106/build/bootstrap-advice-plan/`.
The staging-coupled fixture selected 1163 modules. Its native cache argument did
not override the pre-existing default HIR cache. The owner cancelled only
process group 1608437 with TERM; exec status 143. Captured PIDs 1608437,
1608448, 1616314 and 1658187 were confirmed absent, and a scoped process audit
found no survivors. `isolation-rejected.sdn` and `cleanup-audit.sdn` retain the
classification. Shared cache data was not removed. Zero assertions ran.

Attempt 2: `/home/yoon/dev/simple-bootstrap-advice-plan-fix-20261106/build/bootstrap-advice-plan/baseline2/`.
The actual production planner was separated from staging with original
four-argument behavior for the baseline. This reduced selected modules from
1163 to 323. Explicit private frontend, HIR and native paths were supplied;
the HIR log confirms the private path. Compilation reached native codegen,
then failed with exit 1 and `all_stopped=true`:

`E-BACKEND-CRANELIFT-CALL-ABI`: `parser_cli.parse_cli_option_value` passes f64 to
`_AstExpr.nodes.expr_float_lit`, while its text parameter is represented as
i64 in the native ABI. See `build.log` lines 4848–4854 and `result.sdn`. Zero assertions ran.
This exposed a source caller defect: `expr_float_lit` expects the original text
lexeme, while `parser_cli` passed `fval.to_float()`. PR #7269, merge
`457e9c7b7f7a48bfa7280fa901ed6776d46da613`, corrected the caller to pass `fval`.
This compilation failure was not an advice-regression result.

Both attempts used immutable opus10 Phase 2 SHA256
`43f9a6fc68ac232fcb3d28b0a28ada8fba5b04f5e16326e8f122d09208671c5f`, its matching
runtime capsule, Cranelift and explicit whole-program fixture mode. Neither
produced a valid executable assertion result. No further old-producer build
was launched. Count these as attempts 1 and 2; changing worktrees does not
reset the repair budget.

The actual advice-union fix and streaming caller are restored in the fix
worktree. The native fixture now has nine intended checks, including the
existing four-argument default. Its after invocation explicitly supplies advice
roots; do not call the before/after fixture invocations identical.

A newer producer has separate Hello build/run evidence: SHA256
`ffe83fd87c69573a1ca93e24134e46bbe754be7dff2de2f0eeefc4cf60c9037a` at
`/home/yoon/dev/simple-advice-lexical-scan-20261106/build/mirgen2-probe/authority/simple`,
with runtime sibling `authority/runtime`. Parent recorded normal per-file
Cranelift Hello build/run exits 0, both quiescent. That is a candidate for the
next isolated baseline and repair fixture, not full admission or an advice PASS.

Attempt 3 was a guard preflight refusal: interval 250 ms exceeded the supported
1–100 ms range. No compiler launched; `guard-preflight-rejected.log` is retained
under the before worktree `build/bootstrap-advice-plan-new/before/`.
Attempt 4 uses the established canonical timeout guard with default 100 ms,
enforced 24 GiB ceiling, 1200 s timeout and 10 s grace. The isolated before
worktree includes the merged parser caller fix on release base
`f50693b310067c6e3a4db5b24dc633676d8a7f87`; frontend, HIR, native and temporary
paths are private. It uses the newer producer above, Cranelift, explicit
whole-program fixture mode and disabled TLDR staging switches; the fixture
still invokes the actual production planner/readiness owners. It terminated with exit 1, `quiescent=1`, and peak RSS 10,549,924 KiB.
Native codegen completed 284 modules plus 37 cache hits, with two failures:
`extend_decls` imports non-public `enum_module_body.PENDING_CLOCKED_ARGS`;
`parser_decls_use` imports non-public `fn_struct_decls.file_generic_constraint_modes`.
Cranelift requires visibility-preserving accessor support for these statics.
The exact logs, `build.sh`, `build.env` and native AOT diagnostics are retained
at `/home/yoon/dev/simple-bootstrap-advice-plan-before-20261106/build/bootstrap-advice-plan-new/before/`.
No assertion executable was produced. Attempt 5 (after) was not launched;
the next scoped verification needs these caller/visibility boundaries repaired
or a qualified producer that supports them. Four attempts have been consumed.

Full woven advice execution and helper-object scheduling remain next-producer
qualification gates. Summary readiness alone does not establish a complete
linked program or admit Phase 3. Existing compiler/core/library/MCP runtime
checks also remain pending the qualified full CLI.
