# Bug: `index_of` returns nil on digit-leading string literals (JIT run path)

Status: OPEN
Observed: 2026-07-22
Severity: P2 — wrong results on a common stdlib call; found while probing the
sspec false-green fix

## Symptom
On the self-hosted native binary (`simple run`, JIT path):

```spl
"28 total".index_of("total")            # → nil   (WRONG; expected 3)
" 28 total".index_of("total")           # → 4     (correct)
"x total".index_of("total")             # → 2     (correct)
"Results: 74 total".index_of("total")   # → 12    (correct)
```

Only receivers that are **string literals starting with a digit** fail; the
same content reached via runtime construction behaves correctly (the test
runner's parse path is unaffected because its lines start with `Results:`).

## Suspected mechanism
Literal interning/caching appears to treat digit-leading literals specially
(numeric-looking literal → wrong runtime representation for method dispatch).
Related family: tag-box/char-code literal quirks previously filed.

## Repro
```spl
fn main():
    val a = "28 total".index_of("total") ?? -99
    print("a={a}")   # prints a=-99 on affected binary
```
Binary: self-hosted full CLI (built 2026-07-20, wt_e2ebootstrap).

## Impact
Any `.index_of`/search on digit-leading literals silently misses. Audit other
string methods (`contains`, `starts_with`) for the same literal class before
relying on them in tests.
