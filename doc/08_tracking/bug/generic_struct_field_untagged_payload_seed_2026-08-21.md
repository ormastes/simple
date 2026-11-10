# Generic fn returning scalar `T` yields untagged payload (value * 8) on the seed (2026-08-21)
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Found by:** A7 perf-baseline fixture authoring (`test/05_perf/compiler_hardening/wall_generic.spl`).
**Binary:** `bin/release/x86_64-unknown-linux-gnu/simple` (Rust seed, 59867576 bytes, 2026-08-21 05:10:21 +0000), `bin/simple run`.
**Status:** SUPERSEDED. Not fixed here; belongs to the hardening mono lane (design §18.4).

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


---

## Addendum 2026-11-11 — lane seed2 — verdict SUPERSEDED

Triage-first pass, batch 2, judged against the refreshed seed (bin/simple.exe,
build-commit `0791c2b7f4a7`, 2026-11-11 refresh #8184).

**Root-cause fix confirmed merged:** `fd40b997a913` (2026-08-21, "fix(seed):
multi-line lambda bodies now execute in filter/map/any/all/find/reduce; JIT
generic scalar return/field boxing (T<<3) fixed") — the "T<<3" hunk is exactly
this row's `value << 3` mechanism. It ships the pinned reproduce spec
`test/01_unit/compiler/jit_generic_return_scalar_boxing_spec.spl` with the
class neighbours this row demanded. `git merge-base --is-ancestor fd40b997a913
0791c2b7f4a7` -> YES.

**Seed-smoke (this lane's proof), two independent runs:**
1. The row's own minimal repro (plus neighbours) via
   `SIMPLE_LIB=src SIMPLE_BINARY=$PWD/bin/simple.exe bin/simple.exe run
   /tmp/p3seed2/gen_payload.spl`:
   `ident_i64=2` (buggy: 9), `combine01=1` (buggy: 8), `pair_i64_a=5`
   (buggy: `<value:0x5>`), `ipair_a=5` — all correct in the default (JIT)
   lane, the exact lane the row filed against.
2. Pin spec
   `SIMPLE_LIB=src SIMPLE_BINARY=$PWD/bin/simple.exe bin/simple.exe test
   test/01_unit/compiler/jit_generic_return_scalar_boxing_spec.spl
   --mode=interpreter --no-cache` -> `outcome=OK ... passed=6 failed=0`.

**Cycles:** 0 (no live defect on the refreshed seed). Evidence:
`build/review/p3fix-seed2-20261111.sdn`.
