# Bootstrap host reserve detail design

1. Select known host free memory as the reserve's base; otherwise use the
   known compiler cap as the existing conservative fallback.
2. If neither base is known, preserve the declared-budget return behavior.
3. Refuse a base at or below reserve by returning zero.
4. Subtract reserve, clamp to any positive enforced cap, then clamp to any
   positive declared budget.

Example: declared/cap 25,165,824 KiB, free 97,608,600 KiB and reserve 25,165,824
KiB now yield 25,165,824 KiB, instead of zero. Conversely, a 64 GiB cap with
30 GiB free and 24 GiB reserve now yields 6 GiB, instead of 40 GiB.

The parent reservation is untouched. A 24 GiB tree still fits only one worker
under the existing coordinator allowance and 9,000,000 KiB worker estimate;
this change alone cannot satisfy the current two-worker pool minimum.

Tests import the production helper. The native fixture provides executable
before/after evidence; SSpec covers retained estimate/default rules plus the
new known-host-free cases. See its manual mirror for execution limitations.
