# Pure-Simple oracle-vs-plain divergence sweep — non-print domains (2026-07-29)

Method: `bin/simple run X.spl` (plain = deployed/default engine, currently the
Rust seed since the pure-Simple native harness is not deployed) vs
`SIMPLE_EXECUTION_MODE=interpreter bin/simple run X.spl` (oracle). Divergence =
mismatched output/behavior for the same `fn main()` probe. All probes are
seed-observed proxies for native codegen and need re-confirmation once the
pure-Simple native harness itself is used as "plain". Scope: everything that is
**not** value-printing/formatting (tuple/dict/enum/join/Option print bugs were
covered by prior sweeps and are excluded here).

Read-only lane — no source changes, no commits. Probe files live in
`/tmp/probes/*.spl` (not checked in).

## Divergence table

| probe | domain | oracle (interpreter) | plain (deployed/seed) | diverges? | severity | likely fix area |
|---|---|---|---|---|---|---|
| p01_int_overflow (i64 add) | int arithmetic | `i64::MAX + 1` → `-9223372036854775808` (correct wrap) | → `0` | **YES** | high | native/JIT i64 add overflow codegen (no two's-complement wrap) |
| p04_i32_i64_mix (i32 mul) | int arithmetic | `100000 * 100000` (i32) → `10000000000` (no i32 wrap at all, treated as unbounded) | → `1410065408` (correct i32-wrapped value) | **YES** (interpreter is the wrong side here) | medium | interpreter/HIR: i32 arithmetic not truncated to 32 bits, silently behaves as i64 |
| p03_shift_bitwise | int arithmetic | shl/shr/band/bor/bxor/bnot/neg-shifts all match | match | no | — | — |
| p02_div_mod_neg | int arithmetic | floor-div/mod on negatives match both engines | match | no | — | — |
| p05a/p05b_float_divzero/nan | float | `1.0/0.0` and `0.0/0.0` both **hard-error** `E2001: division by zero` (blocks all further float probes in the same file) | computes IEEE-754 `inf` and NaN-with-`==false` correctly | **YES** (interpreter is the wrong side) | high | interpreter numeric-op dispatch: divide-by-zero check applies int semantics to float division, should special-case float | 
| p05c_is_nan | float | `x.is_nan()` returns `false` for `3.0` | `Runtime error: Function 'f64.is_nan' not found` | **YES** | medium | native/seed runtime missing `f64.is_nan` builtin entirely |
| p09_string_slice (char_count) | string | `s.char_count()` returns correct char counts (11, 6) | `Runtime error: Function 'str.char_count' not found` | **YES** | medium | native/seed runtime missing `str.char_count` builtin entirely |
| p09_string_slice (rest: len/slice/split/replace/find, incl. multibyte) | string | all match (byte-based slice `héll`, byte-offset `find`) | match | no | — | — (byte-vs-char behavior already tracked in memory, not new) |
| p10a_nested_index_assign | collections | `error: semantic: invalid assignment: index assignment requires identifier or field access as container` — **rejects `grid[0][1] = 99` outright** | executes correctly, `grid[0][0]=1`, `grid[0][1]=99` | **YES** (interpreter is the wrong side — feature gap) | medium | interpreter's index-assignment lvalue check doesn't recognize chained `arr[i][j]` as valid container |
| p10b_array_push_reassign | collections | `grid[1] = grid[1].push(5)` → `grid1_len=3` (correct) | **SEGFAULT** (signal 11, exit 139), no error message, silent crash | **YES** | **critical** | native/seed codegen for self-referential array reassign-through-`.push()` — likely a use-after-free/aliasing bug in array reassignment lowering |
| p10c/p10d_dict (int keys, bool keys) | collections | match | match | no | — | — |
| p10e_enum_eq | collections | enum `==` matches (`true`/`false`) both engines | match | no | — | — |
| p06_match_guards | control flow | match (neg/zero/even/odd guard dispatch) | match | no | — | — |
| p07_loop_control (while + nested break/continue) | control flow | match (`early_return=500`, `nested_bc=24`) | match | no | — | — |
| p11d/p11e/p11f_for_return | control flow | `return x` (or `return i`) **from inside a `for x in xs:` loop** returns the correct value (e.g. `777`, `20`, index `1`) | returns a **corrupted value** — e.g. `777`→`6216` (×8), `20`→`80`, index `1`→`0` | **YES** | **critical** | native/JIT lowering of early `return` executed from within a `for`-in loop body — looks like the returned SSA value is a stale/tag-boxed/wrong register, not consistently one multiplier (ruled out clean ×8 tag-box in all cases — needs codegen-level trace) |
| p11c_early_return_option_noloop | control flow / Option | match (`some=40`) — confirms early-return-with-Option alone (no loop) is fine | match | no | — | isolates the p11d/e/f bug to the loop-body-return path specifically, not Option boxing |
| p08_closures (counter/capture) | closures | both engines agree the returned nested-fn counter does NOT increment (`1,1,1` not `1,2,3`) and closure-mutation of a captured `var` does not propagate back (`y` stays `1`) | same (shared bug, not a divergence) | no (both wrong the same way) | n/a (flag separately, not a divergence) | — |
| p11a_option_forloop | Option/control-flow | `find_even` over `[1,3,4,5]` → `Some(4)`; over `[1,3,5]` → `None` | `Some(4)`→ prints as if value `1`; miss case fabricates `Some(1)` instead of `None` | **YES** | critical | same root cause as p11d/e/f (for-loop early return corruption) plus a possible match-dispatch issue on the "miss" (natural loop-fallthrough) path |
| p11b_result_question (`?` chaining) | Result | `chain(-1)` → `Err("negative")` propagated correctly through 2-level `?` | `chain(-1)` → `Ok(5608166920450)` — **`?` fails to short-circuit on `Err`, fabricates a garbage `Ok`** | **YES** | **critical** | native/JIT lowering of the `?` operator / Result short-circuit — does not check the `Err` tag before continuing, or corrupts the propagated value |

## New divergences by domain (excludes prior print/format sweeps)

- **integer arithmetic:** 2 (i64 overflow-wrap-to-0 in native; i32 mul not truncated in interpreter)
- **float:** 2 (float div-by-zero hard-errors in interpreter instead of computing inf/NaN; `f64.is_nan` missing in native)
- **string:** 1 (`str.char_count` missing in native)
- **collections:** 2 (nested `arr[i][j]=v` rejected by interpreter; `arr[i]=arr[i].push(x)` **segfaults** in native)
- **control flow:** 1 (early `return` from inside a `for`-in loop returns a corrupted value in native, both for plain `i64` and `Option<i64>`)
- **Result/Option control flow:** 1 (chained `?` fails to propagate `Err`, fabricates garbage `Ok` in native; likely shares root cause with the for-loop-return bug for the `Option` "miss" case)

Total: **9 new divergences** across 6 domains (plus 1 shared-non-divergent gap noted for closures — both engines silently fail to persist captured-var mutation across calls, worth its own ticket but not an oracle-vs-plain divergence).

## Top 5 highest-value NEW gaps

1. **`arr[i] = arr[i].push(x)` segfaults under native/seed** (p10b). Crash beats every silent-wrong-value bug for severity — any systems code doing in-place array growth via self-index reassignment takes the process down. Likely fix area: array reassignment/aliasing lowering in the native array codegen path (MIR/cranelift array store after a `.push()` that reads-then-writes the same slot).
2. **Early `return` from inside a `for x in xs:` loop returns a corrupted value** (p11d, p11e, p11f, and its Option variant p11a). Reproduces with plain `i64` (rules out Option-boxing as the cause) and is NOT a clean, single multiplier across cases, so it is not simply the already-known tag-box `<<3` bug — it needs its own codegen trace of the for-loop's exit/PHI handling when `return` executes mid-body. This is a bread-and-butter scanning/parsing pattern ("find first match and return it") and is silently wrong, not crashing — the worst combination for systems code correctness.
3. **Chained `?` on `Result` fails to short-circuit on `Err`** (p11b): a 2-level `parse_pos(x)? ; parse_pos(a)?` chain that should stop at the first `Err` instead produces a fabricated `Ok` with a garbage huge value. This breaks the primary error-propagation idiom used throughout Result-based code; likely connected to #2 since both involve control-flow short-circuit exits from a computation that isn't the function's textual last statement.

## Notes / caveats
- All "plain" runs above used the currently-deployed engine (`bin/simple run` → Rust seed w/ JIT-then-interpreter-fallback banner), per the sweep's oracle/plain convention; needs re-confirmation against the pure-Simple native harness directly once that path is fixed/deployed.
- p10b's segfault, p11b's `?`-chain corruption, and p11d/e/f's for-loop-return corruption are new site-level findings distinct from the already-memory-tracked `list.get(i)` `<<3` tag-box family and the `Option<i64>==3` collision family — flagged for a fresh codegen trace rather than assumed to be the same bug, since the multiplier is not consistently ×8.
