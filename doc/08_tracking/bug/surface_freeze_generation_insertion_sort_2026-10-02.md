# Surface-freeze generation row sorting

Status: implementation and behavioral regression specification prepared;
native execution, SSpec and optimizer CLI **UNRUN**. No runtime speedup claim.

Base: release/1.0 commit `1538f7da26270bd58cc8083f37326f1de3ed7160`.
Scope: only sorting the alias/path rows used by
`module_surface_stable_resolution_generation_v1`. No other freeze optimization
or default routing change is included.

`ModuleSurfaceBuilder.finish_into` calls `module_surfaces_freeze`, which computes
one stable resolution generation. The previous insertion sort rebuilt a new
array for each row, copying A(A+1)/2 row references for A aliases. This remains
quadratic even after the earlier fix hoisted generation calculation out of the
per-import loop. A reported long freeze with flat RSS motivated inspection;
that observation does not attribute elapsed time to this particular sort.

The replacement performs stable bottom-up merges. Each pass appends A rows;
there are ceil(log2(A)) passes and at most A comparisons per pass. This is a
static O(A log A) work/reference-copy bound, not measured runtime evidence.
Intermediate pass arrays are not assumed to be reclaimed by the no-GC runtime.
No production comparison counter or instrumentation API was added.

The existing text `<` comparison is unchanged. Equal rows take the left run,
duplicates remain present, the caller's rows are not mutated, and the newline
join plus SHA-256 framing remain unchanged. Empty and singleton arrays require
no merge pass. Doubling stops before integer overflow.

Behavioral coverage:
`test/01_unit/compiler/hir/module_surface_generation_sort_spec.spl` compares the
real helper with the previous insertion-sort oracle for empty/singleton,
sorted/reverse, duplicate, Unicode and uneven merge-run inputs through 256
rows. It also invokes the actual generation function to check alias-order
independence, duplicate preservation, invalid-index filtering and empty digest.

Before admission, run that spec with an admitted self-hosted runtime and retain
its binary/source identity. Compare freeze timing and peak RSS on the same
closure before/after; other known alias-validation and resolver scans remain
outside this patch. Builds and seed execution were explicitly excluded from
this preparation lane.
