# HIR monomorphization actually specializes and rewrites (#158 Phase B)

> `run_monomorphization` was wired as driver Phase 4 but was an expensive no-op:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HIR monomorphization actually specializes and rewrites (#158 Phase B)

`run_monomorphization` was wired as driver Phase 4 but was an expensive no-op:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mono/hir_monomorphization_rewrite_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

```simple
`run_monomorphization` was wired as driver Phase 4 but was an expensive no-op:
`rewrite_module` returned the module unchanged ("For now, return module
unchanged"), so no specialization was ever emitted and no call site was ever
rewritten. Marking a generic as a template is not monomorphizing it.

This spec drives the pass on a hand-built HIR module holding

    fn identity<T>(v: T) -> T: v
    fn main(): identity<i64>(7)

and pins the three things that must be true after Phase 4:

1. a specialized `identity$i64` exists in `module.functions`, with EMPTY
   `type_params` (that emptiness is what a post-Phase-4 sweep checks) and a
   CONCRETE `i64` parameter type substituted for `T`;
2. the generic template is still present (other modules may still call it);
3. `main`'s call site targets the specialization's SymbolId and carries EMPTY
   `type_args`, so nothing downstream of Phase 4 sees a call that still needs
   monomorphizing.

Before the change all three failed: `specializations_created` was 0, no
`identity$i64` function existed, and `main`'s call still named the template
with `[i64]` type arguments.

The module is built by hand rather than parsed on purpose: the Phase A refusal
gates in HIR lowering (`declaration_lowering.spl`) still reject a generic `fn`
outright, so a generic HirFunction cannot be produced from source today. Those
gates stay loud; see
`doc/08_tracking/bug/hir_generic_templates_unconsumed_by_mono_pass_2026-08-21.md`.

```
## Scenarios

### HIR monomorphization pass (#158 Phase B)

#### emits a specialization for identity<i64> instead of returning the module unchanged

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits a specialization for identity<i64> instead of returning the module unchanged
   - Expected: stats.generic_functions_found equals `1`
   - Expected: stats.specializations_created equals `1`
   - Expected: found equals `1`
   - Expected: type_params_left equals `0`
   - Expected: param_is_i64 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits a specialization for identity<i64> instead of returning the module unchanged")
val (result, stats) = run_monomorphization(make_modules())
expect(stats.generic_functions_found).to_equal(1)
expect(stats.specializations_created).to_equal(1)
val out = result["mono_rewrite_test"]
var found = 0
var type_params_left = -1
var param_is_i64 = false
for key in out.functions.keys():
    val f: HirFunction = out.functions[key]
    if f.name == "identity$i64":
        found = found + 1
        type_params_left = f.type_params.len()
        for p in f.params:
            val pt: HirParam = p
            match pt.type_.kind:
                case Int(bits, signed):
                    if bits == 64 and signed:
                        param_is_i64 = true
                case _:
                    pass
expect(found).to_equal(1)
expect(type_params_left).to_equal(0)
expect(param_is_i64).to_equal(true)
```

</details>

#### removes the consumed generic template once its specialization exists (plan 9.3 step 12)

- removes the consumed generic template once its specialization exists (plan 9.3 step 12)
   - Expected: templates equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("removes the consumed generic template once its specialization exists (plan 9.3 step 12)")
# Superseded the earlier "keeps the template" expectation: plan section
# 9.3 step 12 requires a template with >= 1 specialization to stop being
# emittable, and the post-mono verifier counts a surviving one as
# `generic_emitted_definition`. See
# test/01_unit/compiler/mono/mono_template_pruning_spec.spl.
val (result, _) = run_monomorphization(make_modules())
val out = result["mono_rewrite_test"]
var templates = 0
for key in out.functions.keys():
    val f: HirFunction = out.functions[key]
    if f.name == "identity":
        templates = templates + 1
expect(templates).to_equal(0)
```

</details>

#### rewrites the call site to the specialized symbol with no type arguments

- rewrites the call site to the specialized symbol with no type arguments
   - Expected: spec_id > 0 is true
   - Expected: type_arg_count equals `0`
   - Expected: callee_id equals `spec_id`
   - Expected: callee_name equals `identity$i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 49 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rewrites the call site to the specialized symbol with no type arguments")
val (result, _) = run_monomorphization(make_modules())
val out = result["mono_rewrite_test"]
var spec_id = -1
for key in out.functions.keys():
    val f: HirFunction = out.functions[key]
    if f.name == "identity$i64":
        spec_id = f.symbol.id
expect(spec_id > 0).to_equal(true)

var callee_id = -1

var callee_name = ""
var type_arg_count = -1
for key in out.functions.keys():
    val f: HirFunction = out.functions[key]
    if f.name == "main":
        for stmt in f.body.stmts:
            val st: HirStmt = stmt
            match st.kind:
                case HirStmtKind.Expr(e):
                    val et: HirExpr = e
                    match et.kind:
                        case HirExprKind.Call(callee, _, type_args):
                            val ct: HirExpr = callee
                            type_arg_count = type_args.len()
                            match ct.kind:
                                case HirExprKind.Var(sym):
                                    val s: SymbolId = sym
                                    callee_id = s.id
                                # Since 2026-08-22 the repointed callee is a
                                # NamedVar carrying the mangled name: MIR's
                                # lower_call resolves a direct callee by NAME,
                                # and a fresh mono symbol is not in the
                                # caller's symbol table.
                                case HirExprKind.NamedVar(nsym, nname):
                                    val ns: SymbolId = nsym
                                    callee_id = ns.id
                                    callee_name = nname
                                case _:
                                    pass
                        case _:
                            pass
                case _:
                    pass
expect(type_arg_count).to_equal(0)
expect(callee_id).to_equal(spec_id)
expect(callee_name).to_equal("identity$i64")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8200449d7cc14c55a3e214c60591745f84c9793a6e135205b07f414d1d41542b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8200449d7cc14c55a3e214c60591745f84c9793a6e135205b07f414d1d41542b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8200449d7cc14c55a3e214c60591745f84c9793a6e135205b07f414d1d41542b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/mono/hir_monomorphization_rewrite_spec.spl
mirror: doc/06_spec/01_unit/compiler/mono/hir_monomorphization_rewrite_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mono/hir_monomorphization_rewrite_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mono/hir_monomorphization_rewrite_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mono/hir_monomorphization_rewrite_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/mono/hir_monomorphization_rewrite_spec.spl:158:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits a specialization for identity<i64> instead of returning the module unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mono/hir_monomorphization_rewrite_spec.spl:185:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'removes the consumed generic template once its specialization exists (plan 9.3 step 12)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mono/hir_monomorphization_rewrite_spec.spl:202:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rewrites the call site to the specialized symbol with no type arguments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
