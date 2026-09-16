# A same-named `val` later in an `it` body poisons the whole body scope — earlier reads return the registration snapshot

**Date:** 2026-09-05
**Found by:** sspec score-80 wave 4 (modernizing `test/03_system/feature/baremetal/module_var_liveness_class_generalization_spec.spl`)

## Symptom

A module `var` written through a helper, then read BEFORE a later `val`
declaration of the same name in the same `it` body, returns the module var's
**registration-time snapshot** instead of the value just written. The `val`
declaration poisons reads that textually precede it — the whole body scope
resolves the name to the local from the start, but the local's value at those
earlier reads is the stale registration snapshot rather than the live module var.

## Reproduce (verified 2026-09-05, Sep-5 seed `src/compiler_rust/target/bootstrap/simple run`)

```simple
var gi = -999

fn set_i(v: i64):
    gi = v
    0

describe "same-named local poisoning probe":
    it "pre-shadow read returns the helper write, not the registration snapshot":
        set_i(500)
        expect(gi).to_equal(500)   # FAILS: expected -999 to equal 500
        val gi = 3
        expect(gi).to_equal(3)
```

Output: `✗ pre-shadow read … expected -999 to equal 500` — `set_i(500)` ran
first (the sibling scenarios in the spec prove helper writes ARE visible when
no same-named local exists), yet the pre-shadow read sees `-999`.

## Relation to the adjacent record

Same family as
`doc/08_tracking/bug/spec_it_block_reads_stale_module_var_2026-08-04.md`
(it-body reads of module vars returning stale snapshots), but with a distinct
trigger: there the staleness is unconditional; here the read is correct **until**
a same-named local appears anywhere later in the same body. Scope
pre-registration of the local is choosing the snapshot value for the whole body
instead of keeping the module binding live until the declaration point.

## Where the note lives in the tree

`test/03_system/feature/baremetal/module_var_liveness_class_generalization_spec.spl:135-139`
carries a NOTE documenting that the pre-shadow RED was deliberately left out of
the scenario (adding it turns a legitimately-green spec RED for an unrelated
open defect). The generalization arm itself (shadow readback after the `val`)
stays green.

## Unblock condition

A pre-shadow read in the repro above returns `500`; then promote the note in
that spec into a full scenario pair (pre-shadow read = module binding, post-`val`
read = local) in both the spec and its `test/system` twin.
