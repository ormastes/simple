# MIR enum discriminant membership

Frozen acceptance: replace only the prior-discriminant membership scan in
`register_enum_variants` with one local `Dict<i64, bool>`. Preserve folding,
range errors, duplicate error text/span/fatality/order, fallback effective
values after failed folding, names/discriminants order, qualified IDs,
payload metadata, next-value arithmetic, and current-registration early exit.
Insert every value, including invalid and repeated values, after the existing
range check and duplicate diagnostic and before unchanged registration writes.

Old registration performs V(V-1)/2 prior-value comparisons even when there
are no duplicates. The replacement performs one membership probe and one
assignment per variant, with at most distinct(V) local keys. Expected hash
membership work is O(V); dictionary worst-case behavior is not newly claimed.
There is no global cache, synchronization, parallelism, or retained index.

Tests were written before the production edit and exercise actual
parser -> HIR -> `MirLowering.register_enum_variants`, inspecting effective
discriminants, source-ordered fatal diagnostic messages/spans, repeated and
nonadjacent duplicates, negative/portable-limit values, folding failure,
payload metadata, re-registration, and a 2049-variant implicit enum.
The large fixture checks consumer correctness; source inspection establishes
the changed cost mechanism, without a mock work counter.

Base: ordinary successor c4e110dd093fc9268e03888792b03f9322515020.
Before source SHA256: a8577d32aea9abb62de83ad975d52bbd2c2beeaad410ca9c2e15fdecd1d0d326.
Merge owner: enum membership lane. Independent reviewer:
`/root/astra_parallel_memory_review`. Sidecars: N/A.

Qualified runtime tests, optimizer, timing and RSS measurements are UNRUN;
no runtime, release, speed or memory improvement PASS is claimed. The defect
exists in admitted boot6 source, but causation of the current delay remains
UNPROVEN. Live producer inputs and caches are untouched.
