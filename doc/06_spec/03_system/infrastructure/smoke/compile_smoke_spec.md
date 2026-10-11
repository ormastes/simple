# Compile smoke: production frontend and expression emission

**Phase 1 focused diagnostic: PASS, 5/5. Full compiler/native acceptance: OPEN.** Cycle one executed all five production frontend/expression-emission scenarios with the admitted bootstrap seed. The run took 2027 ms, exited 0, observed peak RSS of 390036 KiB, and reported `quiescent=1`. This is bootstrap diagnostic evidence, not native or release qualification. Coverage remains unmeasured; SPipe docgen and zero-stub validation remain pending.

Canonical executable: `test/03_system/infrastructure/smoke/compile_smoke_spec.spl`. Existing requirement: `REQ-INFRASTRUCTU-COMPILE-SMOKE-001`.

## Scope and acceptance boundary

The original smoke file aimed to exercise the `--compile` / `--mode=native` pipeline but asserted only literal arithmetic and string equality. These replacement scenarios test compiler-owned behavior: source is parsed by `parse_module_silent_checked`, parsed nodes are inspected through production AST accessors, and selected parsed expressions are passed to production `cg_expr`. No test-side parser or emitter reproduces the decisions, and no repository source-file substring is treated as execution evidence.

The checked parser returns whether parsing failed (`true` means failure). Its owner explicitly documents this return-value contract as safer across module boundaries than separately consulting `parser_has_errors`. The malformed-input case uses an existing production diagnostic fixture. Parse-success assertions precede AST inspection and expression emission; they do not conditionally gate those calls.

| Production owner | Coverage declaration |
|---|---|
| `src/compiler/10.frontend/core/parser.spl` | 80% target, unmeasured |
| `src/compiler/10.frontend/core/parser_decls.spl` | 80% target, unmeasured |
| `src/compiler/10.frontend/core/parser_expr.spl` | 80% target, unmeasured |
| `src/compiler/10.frontend/core/compiler/cg_expr.spl` | 80% target, unmeasured |

AST accessors are supplied by the existing `compiler.core.ast`, `ast_stmt`, and `ast_expr` owners. `cg_expr` is the expression emitter called by the production AST-to-C++ code generator; these checks do not invoke its whole-program driver.

**Still required for the original acceptance:** an admitted native producer must compile, link, and execute the test artifact, with a retained command, producer identity, exit status, and runtime assertions. Whole-program lowering, full C++ translation-unit emission, object generation, runtime linkage, and generated-code execution remain unverified. Passing these host fixtures cannot close that acceptance or establish cross-backend parity.

## Scenarios

### 1. parses arithmetic precedence and emits the corresponding C++ expression

**Trace:** `REQ-INFRASTRUCTU-COMPILE-SMOKE-001`. **Evidence class:** host-fixture.

1. Parse a function returning an addition with a nested multiplication.
2. Inspect the parsed operator tree and invoke the production expression emitter.

Expected: The parse succeeds. One `arithmetic` function returns i64; its return expression is addition with multiplication on the right and literal operands 1, 2, 3. Production `cg_expr` emits exactly `(1 + (2 * 3))`.

### 2. preserves a text literal and emits its quoted C++ representation

**Trace:** `REQ-INFRASTRUCTU-COMPILE-SMOKE-001`. **Evidence class:** host-fixture.

1. Parse a function returning a quoted text literal.
2. Inspect the literal payload and emit it through the production C++ expression owner.

Expected: The parse succeeds. The function returns text; the AST holds `hello smoke` as a string literal, and production `cg_expr` emits exactly `"hello smoke"`, including quotes.

### 3. retains typed function parameters in declaration order

**Trace:** `REQ-INFRASTRUCTU-COMPILE-SMOKE-001`. **Evidence class:** host-fixture.

1. Parse a function with integer and text parameters.
2. Inspect the production declaration parameter names and type tags.

Expected: The declaration preserves parameter names `[value, label]`, types `[TYPE_I64, TYPE_TEXT]`, and return type `TYPE_I64` in source order.

### 4. rejects a malformed annotation and recovers for the next valid emission

**Trace:** `REQ-INFRASTRUCTU-COMPILE-SMOKE-001`. **Evidence class:** host-fixture.

1. Submit a malformed annotation through the checked parser failure boundary.
2. Parse a valid module and inspect its replacement AST and cleared diagnostic.

Expected: The malformed annotation reports failure and an actual `expected type annotation` diagnostic. A following valid module reports success, clears the parser diagnostic, replaces the declaration with `recovered`, and emits `9`. The captured earlier diagnostic remains intact.

### 5. clears declarations when a following module is empty

**Trace:** `REQ-INFRASTRUCTU-COMPILE-SMOKE-001`. **Evidence class:** host-fixture.

1. Populate the production declaration arena with two functions.
2. Parse empty input and check that no previous declarations or diagnostics survive.

Expected: The first module produces exactly `first` and `second`. Parsing empty input succeeds, resets declaration count to zero, and leaves no first-error diagnostic.

## Evidence and duplicate handling

The coordinator ran cycle one once with `--mode=interpreter --no-session-daemon --no-cache --no-db`; the retained summary reports five passed, zero failed. The producer and 113 frozen frontend files were verified before and after the run. The admitted seed SHA-256 is `0cceac635e63781b7bf9bc9830735e948986de223434eca46d84eb35233f8b17`. The receipt's `max_rss_kib=5859375` is the configured cap; `peak_rss_kib=390036` is the observed peak. No green case was rerun for this documentation update.

| Retained evidence | Repository-relative path |
|---|---|
| Input manifest and producer provenance | `build/phase-one-storage-gui-diagnostic/compile-smoke-cycle-one-inputs.sdn` |
| Exact diagnostic command | `build/phase-one-storage-gui-diagnostic/compile_smoke_spec/cycle-one.command.sdn` |
| Scenario output and 2027 ms summary | `build/phase-one-storage-gui-diagnostic/compile_smoke_spec/cycle-one.log` |
| Exit status 0 | `build/phase-one-storage-gui-diagnostic/compile_smoke_spec/cycle-one.exit` |
| RSS observation, session integrity, and quiescence | `build/phase-one-storage-gui-diagnostic/compile_smoke_spec/cycle-one.rss.env` |

These receipts establish only the five scoped host-fixture checks. They do not establish full compiler lowering, native compile/link/run, measured 80% coverage, or completed manual generation.

The removed legacy `test/system/smoke/compile_smoke_spec.spl` had an exactly matching executable `describe` body, SHA-256 `4fd844b4e0e8348506d2392f3252d2860a0e1b0abe51c0d282dc9b6ee34a4172`. Whole files differed only in the canonical documentation wrapper and unused `step` import. The original native pipeline intent is retained above as OPEN.

<details>
<summary>Complete executable SSpec</summary>

```simple
# @cover src/compiler/10.frontend/core/parser.spl 80%
# @cover src/compiler/10.frontend/core/parser_decls.spl 80%
# @cover src/compiler/10.frontend/core/parser_expr.spl 80%
# @cover src/compiler/10.frontend/core/compiler/cg_expr.spl 80%
# Coverage percentages are targets, not measured results.
# @req REQ-INFRASTRUCTU-COMPILE-SMOKE-001
# codex-system-test
# Host-fixture production frontend and C++ expression emission smoke.
# Original --compile / --mode=native compile-link-run acceptance remains OPEN.

use std.spec.{describe, it, expect, step}
use compiler.core.parser.{parse_module_silent_checked, parser_first_error_get}
use compiler.core.ast.{
    decl_count, decl_get_tag, decl_get_name, decl_get_body,
    decl_get_param_names, decl_get_param_types, decl_get_ret_type, DECL_FN
}
use compiler.core.ast_stmt.{stmt_get_tag, stmt_get_expr, STMT_RETURN}
use compiler.core.ast_expr.{
    expr_get_tag, expr_get_int, expr_get_str, expr_get_left, expr_get_right,
    EXPR_INT_LIT, EXPR_STRING_LIT, EXPR_BINARY
}
use compiler.core.compiler.cg_expr.{cg_expr}
use compiler.core.tokens.{TOK_PLUS, TOK_STAR}
use compiler.core.types.{TYPE_I64, TYPE_TEXT}

describe "Compile smoke production frontend and expression emission":
    it "parses arithmetic precedence and emits the corresponding C++ expression":
        # @req REQ-INFRASTRUCTU-COMPILE-SMOKE-001
        step("Parse a function returning an addition with a nested multiplication")
        val failed = parse_module_silent_checked("fn arithmetic() -> i64:\n    return 1 + 2 * 3\n", "compile_smoke_arithmetic.spl")
        expect(failed).to_equal(false)
        expect(decl_count()).to_equal(1)
        expect(decl_get_tag(0)).to_equal(DECL_FN)
        expect(decl_get_name(0)).to_equal("arithmetic")
        expect(decl_get_ret_type(0)).to_equal(TYPE_I64)
        val body = decl_get_body(0)
        expect(body.len()).to_equal(1)
        expect(stmt_get_tag(body[0])).to_equal(STMT_RETURN)
        step("Inspect the parsed operator tree and invoke the production expression emitter")
        val expression = stmt_get_expr(body[0])
        expect(expr_get_tag(expression)).to_equal(EXPR_BINARY)
        expect(expr_get_int(expression)).to_equal(TOK_PLUS)
        val left = expr_get_left(expression)
        expect(expr_get_tag(left)).to_equal(EXPR_INT_LIT)
        expect(expr_get_int(left)).to_equal(1)
        val product = expr_get_right(expression)
        expect(expr_get_tag(product)).to_equal(EXPR_BINARY)
        expect(expr_get_int(product)).to_equal(TOK_STAR)
        expect(expr_get_tag(expr_get_left(product))).to_equal(EXPR_INT_LIT)
        expect(expr_get_int(expr_get_left(product))).to_equal(2)
        expect(expr_get_tag(expr_get_right(product))).to_equal(EXPR_INT_LIT)
        expect(expr_get_int(expr_get_right(product))).to_equal(3)
        expect(cg_expr(expression)).to_equal("(1 + (2 * 3))")

    it "preserves a text literal and emits its quoted C++ representation":
        # @req REQ-INFRASTRUCTU-COMPILE-SMOKE-001
        step("Parse a function returning a quoted text literal")
        expect(parse_module_silent_checked("fn greeting() -> text:\n    return \"hello smoke\"\n", "compile_smoke_text.spl")).to_equal(false)
        expect(decl_count()).to_equal(1)
        expect(decl_get_name(0)).to_equal("greeting")
        expect(decl_get_ret_type(0)).to_equal(TYPE_TEXT)
        val body = decl_get_body(0)
        expect(body.len()).to_equal(1)
        expect(stmt_get_tag(body[0])).to_equal(STMT_RETURN)
        step("Inspect the literal payload and emit it through the production C++ expression owner")
        val expression = stmt_get_expr(body[0])
        expect(expr_get_tag(expression)).to_equal(EXPR_STRING_LIT)
        expect(expr_get_str(expression)).to_equal("hello smoke")
        expect(cg_expr(expression)).to_equal("\"hello smoke\"")

    it "retains typed function parameters in declaration order":
        # @req REQ-INFRASTRUCTU-COMPILE-SMOKE-001
        step("Parse a function with integer and text parameters")
        expect(parse_module_silent_checked("fn typed(value: i64, label: text) -> i64:\n    return value\n", "compile_smoke_parameters.spl")).to_equal(false)
        expect(decl_count()).to_equal(1)
        expect(decl_get_tag(0)).to_equal(DECL_FN)
        expect(decl_get_name(0)).to_equal("typed")
        step("Inspect the production declaration parameter names and type tags")
        expect(decl_get_param_names(0)).to_equal(["value", "label"])
        expect(decl_get_param_types(0)).to_equal([TYPE_I64, TYPE_TEXT])
        expect(decl_get_ret_type(0)).to_equal(TYPE_I64)

    it "rejects a malformed annotation and recovers for the next valid emission":
        # @req REQ-INFRASTRUCTU-COMPILE-SMOKE-001
        step("Submit a malformed annotation through the checked parser failure boundary")
        expect(parse_module_silent_checked("val broken: = 1\n", "compile_smoke_invalid.spl")).to_equal(true)
        val diagnostic = parser_first_error_get()
        expect(diagnostic).to_contain("expected type annotation")
        step("Parse a valid module and inspect its replacement AST and cleared diagnostic")
        expect(parse_module_silent_checked("fn recovered() -> i64:\n    return 9\n", "compile_smoke_recovered.spl")).to_equal(false)
        expect(parser_first_error_get()).to_equal("")
        expect(decl_count()).to_equal(1)
        expect(decl_get_name(0)).to_equal("recovered")
        val body = decl_get_body(0)
        expect(body.len()).to_equal(1)
        expect(stmt_get_tag(body[0])).to_equal(STMT_RETURN)
        expect(cg_expr(stmt_get_expr(body[0]))).to_equal("9")
        expect(diagnostic).to_contain("expected type annotation")

    it "clears declarations when a following module is empty":
        # @req REQ-INFRASTRUCTU-COMPILE-SMOKE-001
        step("Populate the production declaration arena with two functions")
        expect(parse_module_silent_checked("fn first() -> i64:\n    return 1\n\nfn second() -> i64:\n    return 2\n", "compile_smoke_pair.spl")).to_equal(false)
        expect(decl_count()).to_equal(2)
        expect(decl_get_name(0)).to_equal("first")
        expect(decl_get_name(1)).to_equal("second")
        step("Parse empty input and check that no previous declarations or diagnostics survive")
        expect(parse_module_silent_checked("", "compile_smoke_empty.spl")).to_equal(false)
        expect(decl_count()).to_equal(0)
        expect(parser_first_error_get()).to_equal("")
```

</details>
