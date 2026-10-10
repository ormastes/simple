# Seed interpreter: `(dict[k] ?? 0) + 1` on a missing key yields 4, not 1

Status: OPEN — reproduced 2026-10-10 on `C:/dev/simple-bootstrap-storage/seed-head/simple.exe`
(Rust seed, Windows) against `release/1.0` @ 0c0b130f737. Pure-Simple self-hosted
behaviour not measured on this host.

## Reproduction

```simple
fn main() -> i64:
    var counts: Dict<text, i64> = {}
    val prev = counts["a"] ?? 0
    print "prev={prev}"            # prints: prev=nil   (expected 0)
    counts["a"] = prev + 1
    val got: i64 = counts["a"]
    print "got={got}"              # prints: got=4     (expected 1)
    var c3: Dict<text, i64> = {}
    val miss = c3["zz"]
    print "miss_is_nil={miss == nil}"   # prints: true — the miss IS nil,
                                         # so `?? 0` should have coalesced it
    0
```

`bin/simple run` of the above with the seed prints `prev=nil`, `got=4`. The
`??` operator does not coalesce the `Dict<text, i64>` miss, and `nil + 1`
then evaluates to `4` instead of failing.

## Impact

Any product code that counts with the idiomatic
`dict[k] = (dict[k] ?? 0) + 1` is wrong under the seed. Concretely,
`stage4_derive_compiler_backfill_manifest`
(`src/compiler/70.backend/backend/stage4_symbol_closure.spl`) counts symbol
definitions this way and therefore rejects a single-definition nm scan with
`export '<sym>' must be defined exactly once` when run through the seed — on
release code *without* the Stage4 v2 admission change. This is why
`test/04_smoke/native_stage4_backfill_v2_manifest.spl` cannot produce
pass-after evidence on this host; the smoke needs the self-hosted compiler.

## Not done here

No workaround was normalized into product code (CLAUDE.md: fix the form or
record it). The seed is bootstrap-only; the fix belongs in the Rust seed's
`??` / Dict-miss evaluation, or the expression should be re-verified on the
self-hosted binary before deciding where the defect lives.
