# Self-host native-codegen frontier map (#138/#99)

Generated 2026-07-12 via isolated worktree `/tmp/wt_frontier` (detached at
origin/main `bbfbd6b7865`), driving `bin/release/x86_64-unknown-linux-gnu/simple
native-build --entry <src> -o <bin> --clean` with `SIMPLE_BOOTSTRAP` unset
(mirrors `scripts/check/native-smoke-matrix.shs`), CWD = the worktree so the
seed interprets that tree's pure-Simple compiler.

| Feature | File | Expected rc | Verdict | Detail |
|---|---|---|---|---|
| (a) enum construct + match w/ payload extraction | `a_enum_match.spl` | 7 | **PASS** | rc=7 |
| (b) struct method chains | `b_struct_method_chain.spl` | 3 | **BUILD-FAIL** | `[ERROR] MIR error: MIR lowering error: unresolved method call: value` — the *last* call in `c.inc().inc().inc().value()` fails to resolve; MIR lowering loses the receiver type across the chain of `.inc()` calls (matches documented limitation "chained methods on erased receivers") |
| (c) trait default method dispatch | `c_trait_default.spl` | 3 | **BUILD-FAIL** | `[ERROR] MIR error: MIR lowering error: unresolved method call: greet` — calling a trait's *default-bodied* method (`greet`, which itself calls the required `name()`) through a struct that only overrides `name` does not resolve in native MIR lowering |
| (d) generic fn `<T>` | `d_generic_fn.spl` | 9 | **BUILD-FAIL** | LLVM backend emits invalid IR for the monomorphized generic: `llc-18: error: void type only allowed for function results` / `%t0 = bitcast void %l2 to i64` — a real codegen bug in generic-fn lowering to LLVM, not a source-syntax issue (MIR lowering itself succeeded; `llc` rejected the `.ll`) |
| (e) closure capturing a local | `e_closure_capture.spl` | 7 | **PASS** | rc=7 |
| (f) `Dict<text,i64>` insert+lookup | `f_dict_text_i64.spl` | 7 | **PASS** | rc=7 |
| (g) `[i64]` map/filter/fold | `g_array_map_filter_fold.spl` | 24 | **BUILD-FAIL** | `[ERROR] MIR error: MIR lowering error: unresolved method call: map` (+ `filter`, `fold` — all three unresolved in the same run); `[mir-lower] WARNING: unresolved method call '...' lowered to const-0 placeholder (silent-null risk, Task #145)` fires for each |
| (h) `Result`/`?` propagation | `h_result_try.spl` | 7 | **PASS** | rc=7 |
| (i) nested `for` + `break`/`continue` | `i_nested_for_break_continue.spl` | 12 | **TIMEOUT (hang)** | Build succeeds (binary produced, clean build log, no errors/warnings beyond unrelated deprecation notices). Executing the binary hangs indefinitely — reconfirmed standalone with `timeout 5`, rc=124 both times. Real native miscompile: break/continue control flow inside a nested for-loop produces an infinite loop in the emitted code |
| (j) string interpolation w/ numeric + concat | `j_string_interp_concat.spl` | 4 | **PASS** | rc=4 |

## Summary

- **PASS (6/10):** enum construct+match, closure capture, Dict<text,i64>, Result/`?`, string interpolation, (and the sanity arithmetic case used to validate the invocation form).
- **Real blockers found (4/10), all genuine #138/#99 candidates — not test-authoring mistakes:**
  1. **Chained struct method calls** lose receiver type after 2+ hops (`b_struct_method_chain.spl`) — MIR lowering "unresolved method call: value".
  2. **Trait default-method dispatch** through a struct impl doesn't resolve in native MIR lowering (`c_trait_default.spl`) — "unresolved method call: greet".
  3. **Generic `fn<T>` monomorphization → LLVM** emits invalid IR (void-typed bitcast), `llc` rejects it (`d_generic_fn.spl`).
  4. **Array `map`/`filter`/`fold`** (builtin higher-order array methods) are entirely unresolved in native MIR lowering (`g_array_map_filter_fold.spl`) — all three fail in one file, each silently placeholdered to const-0 per the existing Task #145 warning before hard-failing.
  5. **Nested `for` + `break`/`continue`** builds cleanly but the emitted binary **hangs forever** (`i_nested_for_break_continue.spl`) — this is worse than a build failure since it produces a silently-wrong artifact; worth flagging as highest priority since it's a miscompile, not just a missing feature.

Sources are the exact `*.build.log` / binary exit codes captured under
`/tmp/wt_frontier/frontier/` during the run (worktree removed after this file
was written; rerun the battery to regenerate raw logs if needed).
