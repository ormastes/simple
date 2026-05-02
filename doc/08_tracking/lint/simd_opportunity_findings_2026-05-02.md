# SIMD Opportunity Lint — Findings Report 2026-05-02

**Wave:** L (L2 sub-task)
**Operator:** Claude Sonnet 4.6

---

## §1 Summary

The SIMD-opportunity lint pass (11 rules, L-SIMD-001..011) written by J5/K4 has been wired into `bin/simple lint --simd <file>` via two commits:

- `956d079d74` — `lint_simd.spl` EasyFix adapter + export chain through `rules/impl/__init__.spl` and `rules/__init__.spl`; `--simd` flag added to `src/app/io/cli_lint_commands.spl` (later found to be dead code — see §2)
- Follow-up commit — `--simd` flag wired into the live dispatch path `src/app/io/cli_commands.spl`; added `check_simd_opportunities` import and SIMD scan block

**Task spec required ≥20 cited findings.** Actual lint pass produces 0 findings against `src/lib/`. This is the honest result. Padding rejected per project code-style rule. Root causes documented in §4.

---

## §2 Methodology

### CLI dispatch investigation

`bin/simple lint` dispatches through `src/app/cli/main.spl` → `app.io.cli_ops` → `src/app/io/cli_commands.spl::cli_run_lint`. The `cli_lint_commands.spl` file is a parallel implementation exported by `app/io/__init__.spl` but NOT imported by the live dispatch path (`main.spl` imports from `app.io.cli_ops`, not `cli_lint_commands`). The `956d079d74` wiring into `cli_lint_commands.spl` was dead code; the follow-up commit corrects it by wiring into `cli_commands.spl`.

### Linter crash (pre-existing bug)

`bin/simple lint <file>` crashes with `Function 'line' not found` for any file that produces Linter results. This is a pre-existing field-access lowering bug documented in `doc/08_tracking/bug/lint_val_crash_2026-04-28.md` — `result.line` on a loop variable of type `LintResult` dispatches as a function call. The `--simd` scan block is placed before the per-file OK/error reporting, so it executes; the crash occurs later on `result.line` access if the Linter finds issues.

### Standalone driver

A standalone driver `/tmp/simd_lint_driver.spl` was written to invoke `lint_simd_opportunities` directly, bypassing the broken `Linter.lint_source` path:

```
bin/simple run /tmp/simd_lint_driver.spl -- <file.spl>
```

Files scanned via driver: 19 files from `src/lib/` with `for i in 0..N:` range loops (the syntax required by the 11 rules). Result: **0 SIMD opportunities found**.

---

## §3 Findings

**Total SIMD opportunities detected by lint pass across src/lib/: 0**

No findings to cite. See §4 for root cause analysis.

---

## §4 Gap Analysis

Three concrete reasons the lint pass produces zero findings against the stdlib:

### 4.1 Rule scope: `for i in 0..N:` vs `while i < N:` idiom

All 11 rules use `_is_for_range_loop(t)` which detects `for <ident> in 0..` syntax. The Simple stdlib uses `while i < n:` idiom almost exclusively for numeric-index loops. Examples with matching patterns but wrong loop syntax:

- `src/lib/common/signal_processing/types.spl:197`: `result[i] = a[i] + b[i]` inside `while i < n:`
- `src/lib/gc_async_mut/gpu.spl:752`: `result[i] = alpha * x[i] + y[i]` inside `while i < x.len():`
- `src/lib/common/optimization/genetic.spl:17,301`: position/velocity update inside `while i < n:`
- `src/lib/common/optimization/gradient.spl:10,23,45,48`: perturbation loops inside `while i < n:`
- `src/lib/common/signal_processing/analysis.spl:72`: spectrum accumulation inside `while i < n:`

**FR needed:** Extend `_is_for_range_loop` / add `_is_while_range_loop` to detect `while <var> < <expr>:` followed by `<var> = <var> + 1` increment.

### 4.2 L-SIMD-006 `has_src` logic bug

`src/compiler/35.semantics/lint/simd_opportunity_lint.spl` line 594:

```spl
val has_src = _find_substr(body, "[{lvar}]") > _find_substr(body, "[{lvar}] = ")
```

For body `new_ptr[i] = ptr[i]`, `_find_substr(body, "[i]")` and `_find_substr(body, "[i] = ")` both return the position of the FIRST `[i]` (the destination). The condition is `pos > pos` which is always `false`. L-SIMD-006 never fires.

Confirmed: `src/lib/nogc_sync_mut/allocator.spl:564` has `new_ptr[i] = ptr[i]` inside `for i in 0..copy_size:` — correct syntax, correct pattern, but `has_src` is false.

**Bug fix needed:** Replace with `_find_substr(body.slice(eq_idx + lvar.len() + 5), "[{lvar}]") >= 0` to search only the RHS.

### 4.3 `_loop_body_is_safe` excludes function calls

`_loop_body_is_safe` returns `false` for any loop body line where `identifier(` appears. This blocks:
- L-SIMD-004: `out[i] = max(a[i], b[i])` — `max(` is a function call
- L-SIMD-009 (ReLU): `max(a[i], 0.0)` — function call
- L-SIMD-008: any tolower body using `.to_lower()` — method call

This is intentional conservatism but excludes the most common SIMD-opportunity patterns (`max`, `min`, `abs`) in practice.

**FR needed:** Whitelist pure scalar functions (`max`, `min`, `abs`, `clamp`) in `_loop_body_is_safe`.

---

## §5 Recommendations

| Priority | Action | Location |
|----------|--------|----------|
| High | Fix `has_src` bug in L-SIMD-006 (2-line fix) | `simd_opportunity_lint.spl:594` |
| High | Extend rule matching to `while i < n:` loops | All 11 rules |
| Medium | Whitelist `max`/`min`/`abs`/`clamp` in `_loop_body_is_safe` | L-SIMD-004, L-SIMD-008, L-SIMD-009 |
| Low | Extend L-SIMD-003/L-SIMD-011 to while loops for crypto coverage | crypto hot paths |

### Expected findings after fixes

With the `while` loop extension and `has_src` fix applied:

- `src/lib/nogc_sync_mut/allocator.spl:564` → L-SIMD-006 (memcpy)
- `src/lib/common/signal_processing/types.spl:197` → L-SIMD-001 (elementwise add)
- `src/lib/gc_async_mut/gpu.spl:752` → L-SIMD-001 (AXPY `alpha*x[i]+y[i]`)
- `src/lib/common/optimization/gradient.spl:10,23,45,48` → L-SIMD-001 (perturbation loops)
- `src/lib/common/optimization/genetic.spl:17,301` → L-SIMD-001 (position/velocity update)
- `src/lib/common/signal_processing/analysis.spl:72` → L-SIMD-001 (spectrum accumulation)

---

## §6 Files Modified / Created

| File | Change |
|------|--------|
| `src/compiler/90.tools/fix/rules/impl/lint_simd.spl` | NEW — EasyFix adapter bridging `[SimdOpportunityWarning]` → `[EasyFix]` |
| `src/compiler/90.tools/fix/rules/impl/__init__.spl` | Added `export check_simd_opportunities` |
| `src/compiler/90.tools/fix/rules/__init__.spl` | Added `pub use rules.impl.check_simd_opportunities` |
| `src/app/io/cli_commands.spl` | Added `--simd` flag, import, and SIMD scan block to live `cli_run_lint` |
| `src/app/io/cli_lint_commands.spl` | Dead-code copy of same change (not dispatched by main.spl) |
