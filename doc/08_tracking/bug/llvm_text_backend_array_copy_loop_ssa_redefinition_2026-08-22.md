# LLVM text backend: array value-copy loop redefines an SSA local (llc: multiple definition of 'l15') (2026-08-22)

Filed: 2026-08-22
Status: OPEN
Severity: high — blocks native-build of any function that copies an array by value

## Symptom

```
fn main() -> i64:
    var xs = [1, 2]
    val t = xs
    xs.push(9)
    print "alias {t.len()} {xs.len()}"
    0
```

`bin/simple native-build --runtime-bundle core-c-bootstrap ...` →
`llc-20: simple_llvm_*.ll:95:3: error: multiple definition of local value named 'l15'`.
Reproduced on pristine `origin/main` 625c245bafa (after working around the
`hash_text` cache-load failure, see mir_unresolved_method_call_merge_2026-08-22.md).

## Cause (located, not fixed)

`val t = xs` lowers to a value-semantics copy loop (`rt_array_get` /
`rt_array_push` per element). The loop counter is a MIR local that is written
twice (`%l15 = add i64 %l16, 0 ; copy` in the preheader and
`%l15 = add i64 %l21, 0 ; copy` in the latch). The text LLVM backend emits MIR
`Copy` into an existing local as a new SSA definition instead of an alloca
store / phi, so any MIR local assigned in more than one block is invalid IR.
Same-shape `Copy` elsewhere (straight-line code) happens to be single-assignment
and passes. Fix belongs in `70.backend/backend/_MirToLlvm` (mem2reg-style
alloca for multiply-assigned locals) or in the copy-loop emitter.

Found while building the reproduce fixture for the `merge` bug; the aliasing
half of that fixture (`val t = xs; xs = xs + [..]; t unchanged`) is therefore
only verified on the interpret lane until this is fixed.
