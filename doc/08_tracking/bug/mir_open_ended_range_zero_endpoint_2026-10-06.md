# MIR open-ended ranges synthesize an end of zero

Status: under investigation; native behavior not yet independently reproduced.

Source finding: `src/compiler/50.mir/mir_lowering_stmts.spl` sends every HIR Range iterable to `lower_for_range`. This method synthesizes typed zero for a missing end and compares the counter against it. For a positive start this condition rejects the first iteration. The comment says open-ended ranges need the iterator path, but dispatch does not implement that branch.

Required regression: a range beginning at 1 with absent end and an explicit break at 3 must preserve its three iterations when the language admits this form. Inspect actual generated MIR condition CFG and run a native fixture; interpreter-only success cannot qualify MIR.

Related traversal repair: Range bounds are optional in lowering and must be optional in the authoritative HIR declaration. Generated hash, read-only visitor, and fold walker already guard nil at their entry; unconditional callers there were not additional proven crashes. The recorded Any checker core remains the independently proven nil-dereference crash.
