# Canonical enum finalizer duplicate-map undercharge

Source review demonstrated an independent baseline accounting defect in
`canonical_enum_builtin_finalizer_v1.spl`: duplicate detection used `Dict.has`
and assignment for every site while charging a fixed amount per site.
For 256 distinct colliding keys, the pure dictionary's two linear scans require
65,280 probes, already above the available fixed reservation 57,424 before
growth and text-key work. Later charges cannot prepay already executed work.

The repair retains the native dictionary algorithm. The owner loop's index is
an append-only unique-prefix count: duplicates return before insertion. Before
key formatting, membership lookup or insertion it reserves checked
`128*(index+1)^2 + 512*(index+1)` logical work, `16*(index+1)` state and `256*(index+1)` bytes.
This covers two pure dictionary collision scans with at most41-byte decimal
locator comparisons, key materialization and replacement growth. Native resizing reinserts old rows and can have
quadratic collision work; the quadratic term prepays that case. No native
receiver count or uncharged keys snapshot is used. Overflow/exhaustion refuses
before map work. The public finalizer now enforces the existing invocation
`max_sites` limit (the account factory permits at most256); oversized capture
arrays previously bypassed that limit. More conservative prepayment may reject
requests earlier. No performance parity or physical allocator qualification is
claimed without execution.

Focused authored specs exercise the actual map-update helper: one-short refusal
with unchanged ledger, exact sufficient budget, actual duplicate diagnostic,
and distinct sum/product overflow. All executable tests are UNRUN pending a
qualified runtime. This logical-work repair issues no SOURCE receipt.
