# Residual if/`??` merge collection-identity defects (arm64-darwin, 2026-08-24)

Found while fixing the value-position `if` merge element-type loss that caused the
arm64 stage-2 `hc_enc_hir_module` SIGSEGV
(`stage2_hir_codec_segv_is_i32_truncated_heap_ref_2026-08-24.md`). Both findings
below are **pre-existing** — each was measured to be byte-identical before and
after that fix — and neither is fixed here. Recorded rather than normalized.

Measured with the Rust seed at `src/compiler_rust/target/bootstrap/simple`
(2026-08-24 13:34), `native-build`, `SIMPLE_BOOTSTRAP=1`,
`SIMPLE_PROJECT_ROOT` pointed at the repo, each run under its own
`SIMPLE_CACHE_SCOPE` (the native cache is content-keyed; a renamed file with
identical bytes is a cache HIT and silently reuses the previous object).

## 1. `x ?? []` loses collection-ness entirely -> for-in panics

```
class Node:
    items: [SymbolId]        # also reproduces with `[SymbolId]?`
fn enc_node(node: Node) -> i64:
    var acc = 0
    for e2 in (node.items ?? []):
        acc = acc + 1000 + enc_sym(e2)
    acc
```

`SIMPLE_TRACE_DICT_ELEM=1` prints

```
[dict-elem] for-in coll_mir_type=I64 element_type=I64
```

i.e. the `??` result local is not `Array(...)` at all, so `lower_for_iterator`
falls through to its `#143` "non-array iterable" arm and the binary panics:

```
PANIC: for-in over non-array iterables is not supported by native codegen yet (#143)
```

This is a LOUD failure, not silent corruption, and it is a different construct
from the `if`-expression merge (`lower_if` / `lower_if_chain`) that was fixed.
Reproduces with and without `SIMPLE_BOOTSTRAP=1`.

**Not established:** why the real `src/compiler/20.hir/generated/hir_codec.spl`,
which uses `for e2 in (node.domain_blocks ?? [])` extensively, does NOT panic
here — the crashing stage-2 binary reaches the LATER `.keys()` loop in the same
function, so those `??` loops evidently lower to something runnable in the real
build. The minimal fixture differs from the real site in some way that was not
chased. Do not read this record as a claim about the real codec.

## 2. A function-RETURNED if-merge array reads as length 0 with empty elements

```
fn pick_arr(c: bool) -> [i64]:
    if c: [] else: [1, 2, 3]
fn pick_arr_txt(c: bool) -> [text]:
    if c: [] else: ["x", "yz"]
```

Measured output (identical at `origin/main` and with the merge fix applied):

```
alen=0 a0= a2=          # expected alen=3 a0=1 a2=3
slen=0 s0=x s1=yz       # expected slen=2 -- indexing works, len does not
PANIC: for-in over non-array iterables ...   # `for w in s`
```

The merge fix mirrors the arm's `runtime_array_locals` / `runtime_dict_locals`
markings onto the merge slot, which repairs the same shape when the merged local
is consumed IN THE SAME FUNCTION (`(if d == nil: [] else: d.keys()).len()` went
0 -> 2). It does not survive a function return: the returned local is a fresh
local in the caller and carries none of the marking, so `.len()` takes the
static-size path on `Array(elem, 0)` and answers 0.

The general fix is to make array identity a property of the TYPE rather than of
a per-function side table, or to re-mark call results whose declared return type
is an array. Neither was attempted.

## Verdict

FAIL — 2 pre-existing defect(s) recorded, 0 fixed here.
