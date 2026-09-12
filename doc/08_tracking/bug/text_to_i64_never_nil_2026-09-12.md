# `text.to_i64()` never returns nil, so `?? default` is dead code on every call site

- Status: OPEN (2026-09-12) — found while building the fail-closed harness for
  `test/05_perf/interp/while_loop_shape_parity_spec.spl`; out of that lane's
  scope, filed rather than fixed
- Found: 2026-09-12, worktree `simple-perf-3`, branch `work/perf-3-2026-09-12`
- Component: seed interpreter text method `to_i64`
- Binary: seed built from `origin/main` 4a8e716719e,
  `CARGO_TARGET_DIR=/home/yoon/cargo-perf3`, sha256 `13d5781c52fd5ffa...`
- Lane: interpreter (`SIMPLE_EXECUTION_MODE=interpreter`)

## Summary

`to_i64()` is declared to return `i64?` and is used across the tree as
`s.to_i64() ?? <fallback>` — a fail-closed idiom that reads as "if this text is
not a number, use the fallback". It never takes the fallback. Unparseable input
does not produce nil; it produces a plausible-looking integer:

| input | `s.to_i64() ?? -999` | expected |
|---|---:|---|
| `"-1"` | `-1` | -1 |
| `"2000000"` | `2000000` | 2000000 |
| `"0"` | `0` | 0 |
| `""` | **`0`** | -999 |
| `"abc"` | **`0`** | -999 |
| `"X"` | **`88`** | -999 |

`"X"` returning **88** is the character code of `X`, so a one-character
non-numeric string is silently reinterpreted as a codepoint.

## Why this matters

Every `?? default` guard on `to_i64()` in the tree is dead code, and the two
failure modes are exactly the ones that make a test look green:

1. A missing/empty captured field becomes `0`, which passes a `>= 0` or
   `!= -1` sanity check.
2. A short garbage field becomes a number in a plausible range.

A spec that shells out and parses numbers out of a child's stdout therefore
cannot use `to_i64()` to detect a failed capture — the brief's "fail closed on a
0-byte capture" rule cannot be implemented with it. The shape-parity spec above
works around this by emitting an explicit `ok` flag and numeric `-1` sentinels
from the child shell, and never relying on `??`.

## Repro

```sh
cat > /tmp/t.spl <<'EOF'
fn conv(s: text) -> i64:
    s.to_i64() ?? -999

fn main():
    print "neg1={conv(\"-1\")} empty={conv(\"\")} abc={conv(\"abc\")} X={conv(\"X\")}"
EOF
SIMPLE_EXECUTION_MODE=interpreter <seed> run /tmp/t.spl
# neg1=-1 empty=0 abc=0 X=88
```

Note the helper function: writing `"-1".to_i64()` directly inside an
interpolation does not evaluate (the `{...}` is emitted literally), which is a
separate reason the arithmetic has to be hoisted into a named function.

## Fix direction

`to_i64` should return nil for any input that is not a complete, valid decimal
integer (optionally signed), rather than falling back to 0 or to a character
code. Auditing the existing `?? ` call sites is part of the same change: some of
them may be relying on the current "empty means 0" behaviour.
