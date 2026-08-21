# Generic fn returning scalar `T` yields untagged payload (value * 8) on the seed (2026-08-21)

**Found by:** A7 perf-baseline fixture authoring (`test/05_perf/compiler_hardening/wall_generic.spl`).
**Binary:** `bin/release/x86_64-unknown-linux-gnu/simple` (Rust seed, 59867576 bytes, 2026-08-21 05:10:21 +0000), `bin/simple run`.
**Status:** OPEN. Not fixed here; belongs to the hardening mono lane (design §18.4).

## Reproduce (smallest)
```simple
fn ident<T>(a: T) -> T:
    a
fn main():
    var ai: i64 = 0
    ai = ident(ai) + 1     # 1
    ai = ident(ai) + 1     # expected 2
    print "{ai}"
main()
```
Actual: `9` (= 1*8 + 1). Expected: `2`. Each generic call returning an i64 `T`
returns `value << 3` — the tag shift is never undone. `f64` comes back as its
raw bit pattern (prints as a denormal like `0.000…32106460970537`). `text` is
unaffected (pointer payload). Arithmetic inside the generic (`a + b`) shows the
same factor: `combine(0,1)` -> `8`, `combine(8,1)` -> `72`.

Generic struct fields show the same defect in a different coat: with
`struct Pair<T>: a: T`, `Pair(a: 5, b: 6).a` prints `<value:0x5>` and
`Pair(a: 1.5, b: 2.5).a` prints `576179277326712832`; a non-generic
`struct IPair: a: i64` prints `5` correctly.

## Consequences
- `test/05_perf/compiler_hardening/bench_generic.spl` and `wall_generic.spl`
  currently TIME a miscompile. Their numbers are still a valid regression
  baseline for wall/RSS (the guard does not check output), but any claim about
  generic-vs-mono cost from them is void until this is fixed.
- The mono lane must ship a failing-pre-fix reproduce spec plus class
  neighbours (`f64`, `bool`, enum payload `T`, `Pair<T>` field, nested
  `Pair<Pair<i64>>`) per the fixes-need-reproduce rule.
