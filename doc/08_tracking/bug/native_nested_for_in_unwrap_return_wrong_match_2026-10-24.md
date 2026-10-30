# Native codegen: nested `for … in …: for … in opt!: if …: return x` returns the wrong match

**Date:** 2026-10-24 · **Found by:** `.spab` reader spec work · **Status:** open
**Lane:** stage2 `native-build`, x86_64-pc-windows-gnu (prebuilt stage2)

## Symptom
`spab_digest` searched digest entries by (subject, algo) in caller preference
order. With only a sha256 entry present, a request for sha3-256 returned the
sha256 hex (should be ""), and a request for [blake3, sha256] returned "" (should
be the sha256 hex). The same logic written with index `while` loops is correct.

## Minimal repro
```simple
struct D:
    subject: i64
    algo_id: i64
    hex: text

fn find(found: [D]?, subject: i64, accepted: [i64]) -> text:
    if found == nil:
        return ""
    for algo in accepted:
        for d in found!:
            if d.subject == subject and d.algo_id == algo:
                return d.hex
    ""

fn main() -> i64:
    val ds: [D]? = Some([D(subject: 3, algo_id: 1, hex: "ab")])
    print "want_none=[{find(ds, 3, [3])}] want_ab=[{find(ds, 3, [2, 1])}]"
    0
```
Expected `want_none=[] want_ab=[ab]`. Observed (equivalent code in
packed_blob_view.spl): `want_none=[ab]`, `want_ab=[]`.

## Suspects
Loop-variable binding across a nested `for` over an unwrapped optional (`opt!`)
combined with an early `return` from the inner body; the outer loop variable or
the comparison operand appears stale/misbound.

## Workaround
Bind `val xs: [D] = opt!` first and use index `while` loops (as landed in
`src/lib/nogc_async_mut/sosix/packed_blob_view.spl::spab_digest`).
