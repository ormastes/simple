# `with EXPR as NAME:` scoped resource form -- WP-K acceptance

> `with` already has a pre-existing meaning at CLASS-HEADER position:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `with EXPR as NAME:` scoped resource form -- WP-K acceptance

`with` already has a pre-existing meaning at CLASS-HEADER position:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Plan | doc/03_plan/language/resource/resource_parallel_agent_plan_2026-08-06.md (WP-K) |
| Design | doc/05_design/language/resource/resource_sffi_binding_design_2026-08-06.md |
| Source | `test/01_unit/compiler/resource/resource_with_scoped_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Soft-keyword collision, resolved POSITIONALLY

`with` already has a pre-existing meaning at CLASS-HEADER position:
`class X with Read, Write:` (mixin list, `fn_struct_decls.spl`'s
`parse_struct_or_trait_decl`, checked right after the optional `(Parent)`
clause, before the body colon). WP-K adds a SECOND meaning at
STATEMENT-START position inside a function body (`parser_stmts.spl`'s
`parse_statement`, mirroring the `unsafe:`/`danger:` contextual-block
technique already in that function).

These two forms are recognized by two entirely different parser functions,
reached from two entirely different call sites (`parse_struct_or_trait_decl`
is only ever entered while parsing a `class`/`struct`/`trait` declaration's
header; `parse_statement` is only ever entered while parsing a statement
inside a function/block body). No single token-stream position can ever be
interpreted by both parsers, so there is no runtime ambiguity to resolve --
this is the same positional-disambiguation technique WP-A used to make
`resource` a soft keyword with no new reserved token. If statement-start
`with` is NOT followed by `EXPR as NAME:`, the parser backtracks (lexer +
token snapshot restore) and `with` falls through to ordinary
identifier-expression parsing, so it stays usable as a plain identifier
(e.g. a function literally named `with`) everywhere else.

## The desugar

`with ACQUIRE as NAME: BODY` desugars to one nested block:

    val NAME = ACQUIRE
    BODY
    NAME.close()

This reuses WP-E's existing MIR drop-edge machinery (`mir_lowering_stmts.spl`
/ `function_lowering.spl` / `switch_operators_calls.spl`) with ZERO new
per-exit-path code: WP-E already emits a `Drop` for any resource-owned local
at every explicit `return` and at every `?` early-return arm, for the
lifetime of the whole enclosing FUNCTION (not just the nested block) --  so
an early exit from inside BODY is covered automatically once NAME is
registered as a resource-owned local. The trailing `NAME.close()` this
desugar appends covers the one exit WP-E's per-function machinery does not
already give for free: BODY's own normal fall-through (`.close()` lowers to
a consuming Drop and marks NAME consumed, so the function-end sweep does not
double-drop it on that path). If ACQUIRE itself ends in `?` and that `?`
short-circuits (e.g. `with R.open(...)? as x:`), the early-return happens
INSIDE the `val NAME = ACQUIRE` initializer, strictly before NAME is ever
bound -- so the block body never runs and there is nothing to close. See
`resource_with_scoped_mir_drop_spec.spl` for the MIR-level proof of the
drop-edge/close claims; this spec covers parsing + AST shape only.

## A real, load-bearing gap this WP found and closed

WP-E's `resource_owned_locals` registration (the side-table
`emit_pending_resource_drops` walks) only fired at TWO sites: a resource-
typed function PARAMETER, and a `val b = a` MOVE of an ALREADY resource-
owned place. A FRESH acquire result (`val x = R.open(...)`, exactly what
`with`'s desugar produces) took the plain `emit_copy` branch and was never
registered -- meaning a `with`-bound resource would silently get no
automatic drop on an early return/`?` inside its body, with only the
desugar's own trailing `.close()` protecting it. `mir_lowering_stmts.spl`
now also registers a FRESH resource-typed binding (same
`mir_hir_type_is_resource` helper, no new logic), gated on whichever HIR
type actually got remembered on the local (inferred, or the declared
`let_type` when inference found nothing) so an explicitly annotated
`val x: iso Res = fresh_call()` registers too.

## Scenarios

### with-statement: soft-keyword collision with class-header `with` mixin

#### resolves positionally -- both forms parse correctly from the same source

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- resolves positionally -- both forms parse correctly from the same source


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves positionally -- both forms parse correctly from the same source")
val src = "class Box with Read, Write:\n    n: i64\n\nfn take(r: i64):\n    with r as x:\n        print x\n"
val decls = parse_ok(src)
assert_false(parser_has_errors())

val class_decl = find_decl(decls, DECL_STRUCT, "Box")
assert_true(class_decl >= 0)
assert_equal(decl_get_name(class_decl), "Box")

val fn_decl = find_decl(decls, DECL_FN, "take")
assert_true(fn_decl >= 0)
val stmts = with_desugar_stmts(fn_decl)
assert_equal(stmts.len(), 3)
```

</details>

#### keeps `with` usable as a plain identifier (a function literally named `with`)

- keeps `with` usable as a plain identifier (a function literally named `with`)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps `with` usable as a plain identifier (a function literally named `with`)")
# Statement-start `with` NOT followed by `EXPR as NAME:` must
# backtrack cleanly and re-parse as an ordinary call statement.
assert_false(parse_reports_error("fn with(n: i64) -> i64:\n    n\n\nfn call_it() -> i64:\n    with(1)\n"))
```

</details>

### with-statement: desugared AST shape

#### desugars to [val NAME = ACQUIRE, ...BODY, NAME.close()]

- desugars to [val NAME = ACQUIRE, ...BODY, NAME.close()]


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("desugars to [val NAME = ACQUIRE, ...BODY, NAME.close()]")
val src = "fn take(r: i64):\n    with r as x:\n        print x\n"
val decls = parse_ok(src)
val fn_decl = find_decl(decls, DECL_FN, "take")
val stmts = with_desugar_stmts(fn_decl)
assert_equal(stmts.len(), 3)

# [0] val x = r
assert_equal(stmt_get_tag(stmts[0]), STMT_VAL_DECL)
assert_equal(stmt_get_name(stmts[0]), "x")
val acquire_expr = stmt_get_expr(stmts[0])
assert_equal(expr_get_tag(acquire_expr), EXPR_IDENT)
assert_equal(expr_get_str(acquire_expr), "r")

# [2] x.close() -- the normal-fall-through-exit close, present
# unconditionally regardless of what BODY contains (case b).
assert_equal(stmt_get_tag(stmts[2]), STMT_EXPR)
val close_expr = stmt_get_expr(stmts[2])
assert_equal(expr_get_tag(close_expr), EXPR_METHOD_CALL)
assert_equal(expr_get_str(close_expr), "close")
val close_recv = expr_get_left(close_expr)
assert_equal(expr_get_tag(close_recv), EXPR_IDENT)
assert_equal(expr_get_str(close_recv), "x")
```

</details>

#### threads a trailing `?` on ACQUIRE into the val-decl initializer

- threads a trailing `?` on ACQUIRE into the val-decl initializer


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("threads a trailing `?` on ACQUIRE into the val-decl initializer")
# `with R.open(...)? as x:` -- the `?` is part of the ACQUIRE
# expression parsed by ordinary parse_expr(), not with-specific
# code. A failed acquire short-circuits INSIDE this initializer,
# strictly before `x` is ever bound (case e) -- see the MIR-level
# spec for the runtime proof.
val src = "fn take(r: i64):\n    with r.open()? as x:\n        print x\n"
val decls = parse_ok(src)
val fn_decl = find_decl(decls, DECL_FN, "take")
val stmts = with_desugar_stmts(fn_decl)
assert_equal(stmt_get_tag(stmts[0]), STMT_VAL_DECL)
val acquire_expr = stmt_get_expr(stmts[0])
assert_equal(expr_get_tag(acquire_expr), EXPR_TRY)
```

</details>

#### supports a multi-statement BODY between the acquire and the close

- supports a multi-statement BODY between the acquire and the close


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports a multi-statement BODY between the acquire and the close")
val src = "fn take(r: i64):\n    with r as x:\n        print x\n        print x\n"
val decls = parse_ok(src)
val fn_decl = find_decl(decls, DECL_FN, "take")
val stmts = with_desugar_stmts(fn_decl)
# val-decl + 2 body statements + close = 4
assert_equal(stmts.len(), 4)
assert_equal(stmt_get_tag(stmts[3]), STMT_EXPR)
assert_equal(expr_get_str(stmt_get_expr(stmts[3])), "close")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/language/resource/resource_parallel_agent_plan_2026-08-06.md (WP-K)`
- **Design:** `doc/05_design/language/resource/resource_sffi_binding_design_2026-08-06.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `be2d15bd0a2fb63ffa2cf4b3a67c7d4475c4da8c4c19e8c0f92ae91a945af7a0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `be2d15bd0a2fb63ffa2cf4b3a67c7d4475c4da8c4c19e8c0f92ae91a945af7a0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `be2d15bd0a2fb63ffa2cf4b3a67c7d4475c4da8c4c19e8c0f92ae91a945af7a0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/resource/resource_with_scoped_spec.spl
mirror: doc/06_spec/01_unit/compiler/resource/resource_with_scoped_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/resource/resource_with_scoped_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/resource/resource_with_scoped_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/resource/resource_with_scoped_spec.spl:136:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves positionally -- both forms parse correctly from the same source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/resource/resource_with_scoped_spec.spl:152:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps `with` usable as a plain identifier (a function literally named `with`)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/resource/resource_with_scoped_spec.spl:160:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'desugars to [val NAME = ACQUIRE, ...BODY, NAME.close()]' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
