# Qualified Import Call Statement Unit Spec

> Verifies that a module-qualified call reached via `import MODULE` (e.g.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Qualified Import Call Statement Unit Spec

Verifies that a module-qualified call reached via `import MODULE` (e.g.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/qualified_import_call_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies that a module-qualified call reached via `import MODULE` (e.g.
`provider.answer()`, as opposed to `use provider.*` / `use provider.{answer}`)
lowers to a real function call instead of being silently discarded.

Bug: doc/08_tracking/bug/hir_qualified_import_call_statement_dropped_2026-07-29.md
Root cause: `provider.answer()` parses as `ExprKind.MethodCall(receiver:
Ident("provider"), method: "answer", args: [])`, not `ExprKind.Call(Field(...))`
-- the MethodCall arm in hir_lowering/expressions.spl never special-cased a
module-namespace receiver, so it always lowered to `HirExprKind.MethodCall`
on a Module symbol (no runtime receiver, no class method named `answer`),
which is semantically dead even though it survives structurally as the
function body's tail value.

A second, independent finding along the way: a function whose SOLE statement
is a call (qualified or not) always lowers with `body.stmts.len()==0` --
`lower_hir_block`'s tail-value desugar (HirBlock.has/.value) lifts the last
expression-statement of a value-returning function body out of `stmts` into
`value`. That is normal, general HIR shape (verified here for the
UNQUALIFIED control case too), not itself evidence of a drop -- MIR's
`lower_block_expected` reads `block.has`/`block.value` explicitly
(50.mir/_MirLowering/function_lowering.spl).

## Scenarios

### qualified-import call statement lowering

#### qualified call as sole statement lowers to a real call (tail value, not dropped)

- qualified call as sole statement lowers to a real call (tail value, not dropped)
   - Expected: lowering.errors.len() equals `0`
   - Expected: main_fn.body.stmts.len() equals `0`
   - Expected: main_fn.body.has is true
   - Expected: call_args.len() equals `0`
   - Expected: callable.defining_module.unwrap() equals `provider`


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("qualified call as sole statement lowers to a real call (tail value, not dropped)")
val log = qics_make_logger()
val src_provider = "pub fn answer() -> i64:\n    42"
val provider = parse_full_frontend(src_provider, "provider", "provider", log)
val src_consumer = "import provider\nfn main() -> i64:\n    provider.answer()"
val consumer = parse_full_frontend(src_consumer, "consumer_qualified_sole", "consumer_qualified_sole", log)

var modules: Dict<text, Module> = {}
modules["provider"] = provider
var sources: [SourceFile] = []
sources = sources.push(SourceFile(path: "provider", content: src_provider, module_name: "provider"))
val surfaces = qics_build_surfaces(modules, sources)

var lowering = hirlowering_for_module("consumer_qualified_sole", surfaces)
val hir = lowering.lower_module(consumer)

expect(lowering.errors.len()).to_equal(0)
if val main_fn = qics_find_fn(hir, "main"):
    # SOLE statement in a value-returning body -> tail-value desugar:
    # stmts is empty and the call lives in `.value` instead. This is
    # normal HIR shape (see the unqualified control example below),
    # not a drop.
    expect(main_fn.body.stmts.len()).to_equal(0)
    expect(main_fn.body.has).to_equal(true)
    match main_fn.body.value.kind:
        case HirExprKind.Call(callee, call_args, _):
            expect(call_args.len()).to_equal(0)
            match callee.kind:
                case HirExprKind.NamedVar(symbol, _):
                    if val callable = hir.symbols.get_symbol_raw(symbol.id):
                        expect(callable.defining_module.unwrap()).to_equal("provider")
                    else:
                        assert_true(false)
                case _:
                    assert_true(false)
        case _:
            # Fix shape B (loud error) would show up as
            # HirExprKind.Error here instead of a Call -- fail loudly
            # so a regression to the old silent-MethodCall drop (or a
            # switch to the loud-error fix shape) is caught either
            # way, truthfully reflecting what this fix actually does
            # (shape A: correct lowering, not a loud error).
            assert_true(false)
else:
    assert_true(false)
```

</details>

#### qualified call mixed with other statements stays a real call in body.stmts

- qualified call mixed with other statements stays a real call in body.stmts
   - Expected: lowering.errors.len() equals `0`
   - Expected: main_fn.body.stmts.len() equals `1`
   - Expected: main_fn.body.has is true
   - Expected: callable.defining_module.unwrap() equals `provider`


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("qualified call mixed with other statements stays a real call in body.stmts")
val log = qics_make_logger()
val src_provider = "pub fn answer() -> i64:\n    42"
val provider = parse_full_frontend(src_provider, "provider", "provider", log)
# `provider.answer()` is NOT the last statement here, so it stays in
# `body.stmts` (the trailing `99` is what gets tail-value-desugared).
val src_consumer = "import provider\nfn main() -> i64:\n    provider.answer()\n    99"
val consumer = parse_full_frontend(src_consumer, "consumer_qualified_mixed", "consumer_qualified_mixed", log)

var modules: Dict<text, Module> = {}
modules["provider"] = provider
var sources: [SourceFile] = []
sources = sources.push(SourceFile(path: "provider", content: src_provider, module_name: "provider"))
val surfaces = qics_build_surfaces(modules, sources)

var lowering = hirlowering_for_module("consumer_qualified_mixed", surfaces)
val hir = lowering.lower_module(consumer)

expect(lowering.errors.len()).to_equal(0)
if val main_fn = qics_find_fn(hir, "main"):
    expect(main_fn.body.stmts.len()).to_equal(1)
    expect(main_fn.body.has).to_equal(true)
    match main_fn.body.stmts[0].kind:
        case HirStmtKind.Expr(expr):
            match expr.kind:
                case HirExprKind.Call(callee, _, _):
                    match callee.kind:
                        case HirExprKind.NamedVar(symbol, _):
                            if val callable = hir.symbols.get_symbol_raw(symbol.id):
                                expect(callable.defining_module.unwrap()).to_equal("provider")
                            else:
                                assert_true(false)
                        case _:
                            assert_true(false)
                case _:
                    assert_true(false)
        case _:
            assert_true(false)
else:
    assert_true(false)
```

</details>

#### unqualified call regression: sole-statement tail-value shape is unchanged

- unqualified call regression: sole-statement tail-value shape is unchanged
   - Expected: lowering.errors.len() equals `0`
   - Expected: main_fn.body.stmts.len() equals `0`
   - Expected: main_fn.body.has is true
   - Expected: display_name equals `answer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("unqualified call regression: sole-statement tail-value shape is unchanged")
"""Control example: a PLAIN (non-module-qualified) sole-statement
call must show the exact same tail-value shape as the qualified
case above (stmts empty, has=true, value=Call) -- proving the
stmts.len()==0 observation is a general HIR convention, not
something this fix introduced or is masking."""
val log = qics_make_logger()
val src_consumer = "fn answer() -> i64:\n    99\nfn main() -> i64:\n    answer()"
val consumer = parse_full_frontend(src_consumer, "consumer_unqualified_control", "consumer_unqualified_control", log)

var lowering = HirLowering.with_filename("consumer_unqualified_control")
val hir = lowering.lower_module(consumer)

expect(lowering.errors.len()).to_equal(0)
if val main_fn = qics_find_fn(hir, "main"):
    expect(main_fn.body.stmts.len()).to_equal(0)
    expect(main_fn.body.has).to_equal(true)
    match main_fn.body.value.kind:
        case HirExprKind.Call(callee, _, _):
            match callee.kind:
                case HirExprKind.NamedVar(_, display_name):
                    expect(display_name).to_equal("answer")
                case _:
                    assert_true(false)
        case _:
            assert_true(false)
else:
    assert_true(false)
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

- Canonical SPipe generation for source `a6ca16e2419e666103c4820f87e495d4cfb7138e8e8e8bda30037e3bd04be67f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a6ca16e2419e666103c4820f87e495d4cfb7138e8e8e8bda30037e3bd04be67f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a6ca16e2419e666103c4820f87e495d4cfb7138e8e8e8bda30037e3bd04be67f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/hir/qualified_import_call_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/qualified_import_call_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/qualified_import_call_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/qualified_import_call_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/qualified_import_call_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/hir/qualified_import_call_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'qualified call as sole statement lowers to a real call (tail value, not dropped)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/qualified_import_call_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'qualified call mixed with other statements stays a real call in body.stmts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/qualified_import_call_spec.spl:155:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'unqualified call regression: sole-statement tail-value shape is unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
