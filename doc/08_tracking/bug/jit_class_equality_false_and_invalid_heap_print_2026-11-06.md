# BUG: JIT `==` on two equal class objects is false; printing one shows `<invalid-heap:…>`

- **Status:** open
- **Severity:** P2
- **Found:** 2026-11-06, seed-class-reference lane review
- **Lane:** Rust seed, `SIMPLE_EXECUTION_MODE=jit` (tree-walk interpreter is correct)

## Repro

```simple
class P:
    x: i64

fn main():
    val a = P(x: 1)
    val b = P(x: 1)
    print(a == b)
    print(a)
```

Seed `cargo build --release --bin simple` from `origin/release/1.0.0`
`ed2caded61e` plus the class write-back fix (branch
`work/seed-class-reference-20261106`):

| mode | `a == b` | `print(a)` |
|------|----------|------------|
| `SIMPLE_EXECUTION_MODE=interpreter` | `true` | `P(x: 1)` |
| `SIMPLE_EXECUTION_MODE=jit` | `false` | `<invalid-heap:0xfd21ec001431>` |

## Notes

- Two defects: (1) the JIT `print`/`to_text` path does not recognise the
  JIT class-object heap layout and falls back to `<invalid-heap:…>`;
  (2) `==` on class objects disagrees between engines (interpreter compares
  fields, JIT returns false — likely pointer identity or a failed decode).
- Owner decision 2026-11-06 makes classes reference types; whether class
  `==` is structural or identity must be stated by the language spec, but
  the two engines must agree either way, and printing must never show an
  invalid-heap placeholder.
- Not caused by the write-back fix (interpreter-only change).
