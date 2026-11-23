# `simple run` (pure-Simple interpreter) rejects non-text dict keys; `s + v` over `d.values()` lowers to `merge`

Status: open
Found: 2026-11-23, follow-up to `cli_run_interpreting_compiler_frontend_fails_2026-11-23.md` (lane ri1, PR #11059)
Binary: native CLI built from `work/ri1-20261123` (c521a7f5058) with seed `C:/dev/wt/sd1-target/release/simple.exe`

PR #11059 removed the first blockers: the missing bitwise/shift/`in` binops, and the nil-returning `rt_xxh3_128_text`, `rt_text_to_bytes` and `rt_bytes_to_text` externs. The frontend probes now get further and stop at two new interpreter gaps.

## 1. Non-text dict keys
`cli_main.exe run` on the m5/m6 probes (the frontend imports, plus HIR lowering for m6) fails with `Interpret error: dict key must be text`. The interpreter's `Value.Dict` is `Dict<text, Value>`, and both index paths reject other key kinds: `src/compiler/70.backend/backend/interpreter.spl:528` and `interpreter_expr.spl:281`. The frontend uses dicts with i64/enum keys. A fix needs a key encoding or a different Dict value representation. That is a design change, not a one-liner. The current error also does not name the key kind, which is a cheap first fix.

## 2. `s = s + v` where `v` comes from `d.values()`
    val d = {"a": 1, "b": 2}
    var s = 0
    for v in d.values():
        s = s + v
fails with `unresolved method call: merge (receiver kind i64)` at the `s + v` line. `d.values()` itself now works (#11059). The lowering seems to treat `+` on an operand of unknown or Any type as a dict-merge method call. That needs investigating in HIR lowering of `+` when one operand's type is unresolved.
