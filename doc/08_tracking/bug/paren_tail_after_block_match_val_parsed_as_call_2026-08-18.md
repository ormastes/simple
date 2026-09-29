# Parenthesised tail expression after a block-`match` `val` is parsed as a call

Date: 2026-08-18
Status: OPEN
Found by: isolated re-run of `test/05_perf/os/crypto/x25519mlkem768_perf_spec.spl`

## Symptom

```
  ✗ should NFR-008 NFR-011 records cold scalar first-use exchange
    semantic: variable `recovered` not found
  ✗ should NFR-008 NFR-011 records complete scalar hybrid exchange latency
    semantic: variable `recovered` not found
```

## Minimal reproduction (Rust seed, `bin/simple run`)

```simple
fn mk(n: i64) -> Result<i64, text>:
    if n > 0:
        return Ok(n)
    Err("neg")

fn f() -> bool:
    val a = match mk(1):
        case Ok(v): v
        case Err(_): return false
    (a > 0 and a < 10)      # <-- statement starts with '('

fn main() -> i64:
    print "f={f()}"
    0
```

```
[CODEGEN BODY] Function 'f' body compilation failed: GlobalLoad: unresolved
identifier 'a' (not a global, function, const-data name, or import)
error: semantic: value is not callable
```

`value is not callable` is the tell: the `(` line is glued onto the preceding
block-`match` as a CALL argument list, i.e. the source is parsed as
`val a = (match ...)(a > 0 and a < 10)` — so `a` is referenced inside its own
initialiser and is genuinely unbound at that point.

## Controls (all PASS on the same binary — the defect needs the exact combination)

| variant | shape | result |
|---|---|---|
| v1 | block-`match` val + tail WITHOUT parens (`a > 0 and a < 10`) | `v1=true` |
| v2 | `val a = 5` + parenthesised tail | `v2=true` |
| v4 | block-`match` val + one intervening `val` + parenthesised tail | `v4=true` |
| v3 | block-`match` val + parenthesised tail (single line) | **FAIL** |
| v5 | same as v3 but no `return` in the `case` arms | **FAIL** |

So it is neither the `return` inside the arm nor parenthesised tails in general:
it is a statement beginning with `(` **immediately** after a block-bodied
`match` initialiser.

## Scope

Observed on the Rust bootstrap seed (`bin/simple` -> shared
`bin/release/x86_64-unknown-linux-gnu/simple`). Not yet re-checked against a
pure-Simple self-hosted binary — this lane is forbidden from rebuilding or
replacing the shared seed, so the compiler-side fix and its verification are
deliberately NOT attempted here.

## Action taken in this lane

`test/05_perf/os/crypto/x25519mlkem768_perf_spec.spl` had its final expression
in `_scalar_exchange_once()` rewritten to an unambiguous form. **No assertion
was weakened, removed, or reordered** — the returned boolean is the identical
conjunction of the identical two crypto checks (evidence validity and
shared-secret equality). The rewrite exists only to stop the parser mis-binding;
this bug record is the reason it is not a silent workaround.
