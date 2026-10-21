# RT canonical sorting correction

Frozen scope: preserve `rt_sort_text([text]) -> [text]`, native text `<`,
duplicate multiplicity, stable equal ordering, caller input, all diagnostics,
and every `RT-CLOSURE-V1` byte. No graph, root, manifest, hash-scope, or HIR
adapter change is permitted.

The admitted executing-645 source at `/home/yoon/dev/simple-lane-boot6` has
insertion sorting in `rt_criticality.spl:74`. Its digest sorts every fact row;
the adapter can request two digests per admitted root. Ascending/equal rows
require N(N-1)/2 comparisons and reverse rows require that many shifts.
This proves avoidable source work, not the cause of the currently observed
RT phase duration: the admitted adapter first performs a blob census.
Executing-source receipt is retained by the build owner at
`build/native_probe/phase3-postfix-20261021/logged-llvm-producer-rebuild/rt-criticality-executing645-source-pins.json`.

Use stable bottom-up merging into a separately populated scratch array and
indexed copyback into the output. Each level compares at most N elements and
writes at most 2N array slots; there are ceil(log2(N)) levels. Two independent
N-element buffers bound live auxiliary references to O(N); no recursion,
global cache, per-level array allocation, or aggregate buffer rebinding.
Subtract remaining lengths before clamping run bounds; guard doubling width
with `width >= count - width` to avoid integer overflow.

Acceptance regression: executable `rt_criticality_sort_spec.spl` compares the
production function with the frozen insertion oracle across empty, odd,
equal, prefix, signed-text, and Unicode fixtures; a 2049-element fixture
checks duplicates and input preservation. Exact canonical hash bytes and
current/stale capability digest behavior are asserted independently.
The existing `test/01_unit/compiler/semantics/rt_criticality_spec.spl` retains
real current/stale manifest admission tests; those are also UNRUN here.

Merge owner: RT criticality performance lane. Final source reviewer:
`/root/astra_parallel_memory_review`. Sidecars: N/A. Tests were written before
implementation. Qualified runtime tests, optimizer execution, p50/p95 time,
and peak/steady RSS are **UNRUN** because no qualified runner is available;
no measured speedup, memory improvement, verification PASS, or release
admission is claimed. A newly built producer is required to execute this
correction; source edits cannot alter the already running old compiler.
