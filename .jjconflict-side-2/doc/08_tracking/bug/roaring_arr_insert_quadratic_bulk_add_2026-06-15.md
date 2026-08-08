# Bug: roaring arr_insert O(n²) scan on sequential bulk-add causes interpreter timeout

**Date:** 2026-06-15
**ID:** roaring_arr_insert_quadratic_bulk_add_2026-06-15
**Severity:** P2 — test timeout (hang at 120 s); no data corruption
**Component:** src/lib/common/search/roaring.spl — `Container.arr_insert`

## Symptom

`test/01_unit/lib/common/search/roaring_spec.spl` timed out (120 s) every run.
The spec adds 4100 sequential ids (0..4099) to trigger ARRAY→BITMAP promotion,
then adds 8200 sequential ids for the two-chunk test.

## Root Cause

`arr_insert` performs a **linear scan from `pos=0`** to find the insertion point:

```
while pos < n and self.arr[pos] < low:
    pos = pos + 1
```

When ids are inserted in ascending order (0, 1, 2, …, N-1), every call must
scan the entire existing array before reaching the end. Total work = O(N²).

For N = 4100 that is ≈ 8.4 million comparisons in the interpreter; for N = 8200
(second test) ≈ 33.6 million. The interpreter executes roughly 1–5 M operations
per second, so the combined workload exceeds 120 s wall time.

## Minimal Repro

```simple
use lib.common.search.roaring.{RoaringBitmap}
fn main():
    var rb = RoaringBitmap.new()
    var i = 0
    while i < 4100:
        rb.add(i)   # hangs here — triggers quadratic scan in arr_insert
        i = i + 1
    print(rb.cardinality().to_text())
```

## Fix Applied

Added an O(1) fast-path at the top of `arr_insert`: if the array is non-empty
and `low >= arr[n-1]` (i.e. the new element belongs at or past the tail), skip
the scan entirely:

```simple
val n = self.arr.len()
if n > 0 and self.arr[n - 1] <= low:
    if self.arr[n - 1] == low:
        return          # duplicate — already present
    self.arr.push(low)  # strictly greater — append at tail
    return
# fall through to general linear-scan + shift for out-of-order inserts
```

Sequential bulk-add (the common case for range tests) is now O(N) overall.
Out-of-order inserts still use the O(N) linear scan per element (O(N²) worst
case), which is acceptable for the ARRAY container's maximum size of 4096.

## Language-Level Observation

The Simple interpreter has no tiered optimization for sorted-container workloads.
A future stdlib addition of an `arr.insert_sorted(v)` primitive (similar to
Rust's `Vec::insert`) would eliminate the append-then-shift overhead and avoid
the need for this fast-path heuristic. Filed as a stdlib improvement candidate.

## Verification

After the fix, `roaring_spec.spl` completes in ~16 s (interpreter, 32 threads)
with all 150 search specs green. Absolute oracle values confirmed by standalone
probe:
- 4100-entry sequential set → cardinality 4100, BITMAP container, contains(0/4096/4099)=true, contains(4100)=false
- 8200-entry sequential set → cardinality 8200
- AND([1,3,5,7,9], [3,4,5,6,9,10]) → cardinality 3
- OR → cardinality 8
- ANDNOT → cardinality 2
