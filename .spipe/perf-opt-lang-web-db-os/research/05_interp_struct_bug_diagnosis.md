# Diagnosis: interp_cross_module_struct_return_unit_2026-06-13

**Date:** 2026-06-13  
**Investigator:** Claude Sonnet 4.6 (diagnostic pass)  
**Status:** ROOT CAUSE CONFIRMED — fix site identified

---

## Minimal repro + variant results

**Fixture files created:** `test/fixtures/cross_module_struct/`

| Variant | File | Result | Notes |
|---------|------|--------|-------|
| C — control: same-module, no `unit` param | `mod_same.spl` | PASS | baseline works |
| A+B — cross-module struct via constructor fn, no `unit` param | `mod_b_main.spl` | PASS | cross-module struct is fine when no reserved-keyword params |
| REPRO — parameter named `unit` (single-file) | `mod_unit_param.spl` | **FAIL** | both JIT and interpreter |

### Actual minimal repro (single file, no cross-module needed):

```spl
struct MyResult:
    val_field: text

fn make_result(unit: text) -> MyResult:
    MyResult(val_field: unit)

fn main():
    val r = make_result("ops/sec")
    print(r.val_field)
```

Output:
```
[INFO] JIT compilation failed, falling back to interpreter: HIR lowering error: Unknown variable: Unit while lowering make_result
error: semantic: variable `Unit` not found
```

**Key finding:** The bug is NOT about cross-module struct types. It is triggered by any function
parameter named `unit` (lowercase). Cross-module usage in bench_harness.spl just exposed it because
`make_bench_result` has `unit: text` as a parameter.

Variant B (direct struct literal `Foo(x: 42)` in module B) PASSES — cross-module struct type
registration itself works correctly. Variant A (cross-module constructor fn without `unit` param)
also PASSES.

---

## Failure layer

**Two-layer failure, same root cause:**

1. **JIT/HIR layer:** `hir::lower_with_context` is called on the merged AST for bench_baseline_driver.
   The HIR lowerer tries to lower `make_bench_result`'s body. The identifier `unit` in the expression
   `BenchResult(unit: unit, ...)` is parsed as `Expr::Identifier("Unit")` (capital). The HIR lowerer
   calls `ctx.lookup("Unit")` — not found (parameter stored as `"unit"`) — then checks globals — not
   found — then emits `LowerError::UnknownVariable(format!("{name} while lowering {func_name}"))`:
   `"Unit while lowering make_bench_result"`.
   - Emit site: `src/compiler_rust/compiler/src/hir/lower/expr/mod.rs:319`
   - Error definition: `src/compiler_rust/compiler/src/hir/lower/error.rs:17-18`

2. **Interpreter fallback:** After JIT fails, interpreter is invoked. Same parsed AST. Same
   `Expr::Identifier("Unit")` in function body. Variable lookup for `"Unit"` in env also fails:
   `error: semantic: variable \`Unit\` not found`.
   - The interpreter is `src/compiler_rust/compiler/src/interpreter/` (Rust seed interpreter).

---

## Runtime dispatch (seed vs pure-Simple)

`bin/simple run` dispatches via `src/compiler_rust/driver/src/exec_core.rs`:
- `run_file_with_args` tries JIT first (`run_file_jit`), falls back to `run_file_interpreted_with_args`.
- Both paths use the **Rust seed interpreter/compiler** in `src/compiler_rust/`.
- The pure-Simple interpreter at `src/compiler/95.interp/mir_interpreter.spl` is NOT invoked by
  `bin/simple run`; it is the self-hosted stage4 path and requires a different invocation.
- Confirmed by: `exec_core.rs:627` emits the `[INFO] JIT compilation failed...` message; both
  `run_file_jit` and `run_file_interpreted_with_args` live in `exec_core.rs` and call Rust-seed HIR/interp.

---

## Root cause: parser keyword-identifier case mismatch

**File:** `src/compiler_rust/parser/src/expressions/primary/identifiers.rs`  
**Line 74:**
```rust
TokenKind::Unit => self.parse_keyword_identifier("Unit"),  // BUG: capital "Unit"
```

**Compare with** `src/compiler_rust/parser/src/parser_helpers.rs` `expect_identifier()`:
```rust
TokenKind::Unit => "unit".to_string(),   // lowercase "unit" — used for declarations
```

When `unit` appears in an **expression** (body of a function), the primary expression parser sees
`TokenKind::Unit` and calls `parse_keyword_identifier("Unit")` — producing `Expr::Identifier("Unit")`
with a capital U.

When `unit` appears as a **parameter name** (declaration context), `expect_identifier()` is called —
producing the string `"unit"` (lowercase).

Result: parameter is registered in `ctx.locals` under key `"unit"`, but all uses of that parameter
in the function body produce `Expr::Identifier("Unit")`. The lookup `ctx.lookup("Unit")` returns
`None`. Both the HIR lowerer (strict mode) and the interpreter fail.

**Secondary finding:** `TokenKind::Shared` has the opposite situation — both paths use `"Shared"`
(capital), so it is internally consistent and does not cause a bug. `TokenKind::Not` has the reverse
mismatch (expression → `"not"`, expect_identifier → `"Not"`) which could affect operator trait
lookup but is a separate issue.

---

## Ownership verdict

**THE FIX SITE IS IN THE RUST SEED.**

`src/compiler_rust/parser/src/expressions/primary/identifiers.rs` is part of
`src/compiler_rust/parser/` — the Rust seed parser. This is **off-limits** per CLAUDE.md:
> "fix .spl not Rust, don't modify seed unless explicitly asked"

The pure-Simple compiler at `src/compiler/` is the self-hosted target, but it has its own
parser. The bug described here lives exclusively in the Rust seed parser crate, which is used
by `bin/simple run`, `bin/simple test`, and the JIT/HIR lowering pipeline.

**There is no pure-Simple fix path** for this specific bug — the `.spl` sources (bench_harness.spl)
are correct; the parser is what mishandles the `unit` keyword in expression context.

**Verdict: Rust seed — requires explicit authorization to fix.**

---

## Proposed fix + risk

**Fix site:** `src/compiler_rust/parser/src/expressions/primary/identifiers.rs:74`

**Change:**
```rust
// BEFORE (bug):
TokenKind::Unit => self.parse_keyword_identifier("Unit"),

// AFTER (fix):
TokenKind::Unit => self.parse_keyword_identifier("unit"),
```

**Rationale:** All other contextual keywords that are lower-case source tokens use their lowercase
string in `parse_keyword_identifier`. The `"unit"` string is what `expect_identifier()` produces
for declarations, so using `"unit"` in expression context makes the names match.

**Risk assessment:**
- LOW risk for correctness: any code currently using `unit` as a variable/parameter name is
  already broken (Unknown variable error). Changing to lowercase cannot break working code.
- POSSIBLE regression: if any code explicitly looks up a variable named `"Unit"` (capital) and
  stores it under that name (e.g., a global named `Unit` that shadows the unit type concept),
  that would change behavior. A project-wide search for `globals.insert("Unit", ...)` or
  `env.insert("Unit", ...)` shows no such site.
- ALSO CHECK: the `Note` comment in `identifiers.rs` for the `Slice`/`Flat` keywords (line ~78)
  describes the exact same prior fix: "Capitalizing here silently corrupted field names like `slice:`
  into 'Slice' (SliceIter HIR lowering failure, 2026-06-12)." The `unit` fix is the same pattern.
- After the fix, `bench_harness.spl` make_bench_result will work in interpreter mode, and the
  `pending("interp-cross-module-struct-unit")` test in the lang bench spec can be un-pended.

**Workaround** (no code change needed): Rename parameter `unit` to `unit_str` or `metric_unit`
in bench_harness.spl. This avoids the keyword collision without touching the Rust seed.
