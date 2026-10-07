# MIR open-ended ranges synthesize an end of zero

Status: MIR condition repaired; native behavior qualification pending.

Source finding: `src/compiler/50.mir/mir_lowering_stmts.spl` sends every HIR Range iterable to `lower_for_range`. This method synthesizes typed zero for a missing end and compares the counter against it. For a positive start this condition rejects the first iteration. The comment says open-ended ranges need the iterator path, but dispatch does not implement that branch.

Required regression: a range beginning at 1 with absent end and an explicit break at 3 must preserve its three iterations when the language admits this form. Inspect actual generated MIR condition CFG and run a native fixture; interpreter-only success cannot qualify MIR.

The repair omits the fabricated zero endpoint and emits a direct branch to the
body when the end is absent. Existing bounded comparisons and loop
increment/continue/break blocks remain. Two owner-level specs invoke real
`MirLowering.lower_for_range` and inspect its generated condition terminator:
open end is Goto, present end is If. Both pass with the Phase 1 diagnostic seed;
native fixtures must still execute and print 6.

The bare header `for i in 1..:` currently fails parsing. Parenthesized `(1..)`
is accepted and used by the native regression fixture. This grammar failure
remains a concrete separate issue; it is not claimed fixed by the MIR change.

Related traversal repair: Range bounds are optional in lowering and must be optional in the authoritative HIR declaration. Generated hash, read-only visitor, and fold walker already guard nil at their entry; unconditional callers there were not additional proven crashes. The recorded Any checker core remains the independently proven nil-dereference crash.
