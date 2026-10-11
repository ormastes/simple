# Phase 1 SMF cache release fixture scope (2026-10-11)

Status: focused cached bootstrap diagnostic PASS; no production changes.

Current release `4a3644f512135f4a07069fd299536203ac361f06` reproduces 0/4 cases
in `smf_cache_release_failure_spec.spl`. A compression-header helper starts
halfway through the release-refusal fixture. The cache construction therefore
belongs to the wrong function, references an unavailable header, and leaves
`release_refusal_cache` without its required return value.

Move only `compression_header_bytes` below the complete cache fixture. Preserve
all executable assertions and both helper bodies. The existing requirements
NFR-SMF-CACHE-RELEASE-001/002/003 still demand retained records for release retry,
resident byte accounting, historical counters and unchanged absent-path state.
The compression test still checks both absent and unknown tags against None_.

Evidence: `build/phase1-smf-fixture-20261011/baseline-result.json` records 4
executed, 0 passed, exit 1. `fixed-result.json` records 4 executed, 4 passed,
exit 0 in 1.61 seconds. The producer SHA256 is
`15102d32226b3fbead63d3c63e33e99a6f0e9ffcddea06080fb65872445cbafb`.
The fixture intentionally exercises the production facade's zero-address
release refusal; it does not claim an injected OS unmap failure or real mapping.
No compiler rebuild or previously green check replay occurred.

## Remaining loader cohort evidence

The independent grouped triage artifacts
`build/phase1-loader-grouped-triage-20261011/summary.json` and
`current-source-triage.json` retain 49 unresolved loader rows with 153 retained
failed cases. Each row binds its original log hash and current release test hash.
Primary error groups: 16 unavailable API/field rows, 21 behavior/source-contract
rows, 6 rows without executed cases, 3 native mapping/cleanup refusal rows,
2 green-count rows with rejected receipts, and 1 nil file/platform-read row.
These are routing classifications, not proven current root causes or closures.

The global retained candidate queue remains 4758 rows, SHA256
`f1f466039b1007ac75058dbad484ab040e3cd7c9c03be1078049e3e214728c86`.
This focused repair does not remove rows or upgrade the overall qualification.
Missing referenced release artifacts include aspect_final_unpin_registry.spl,
aspect_acquisition.spl, runtime_icache.c and runtime_page_size.c; availability
alone neither implements their contracts nor qualifies their tests.

Cached pure runtime discovery is coordinated with the backend owner. The
corrected pure composition has only LLVM hello diagnostic evidence and is not
admitted for the compiler/core/MCP gates. Production loader PRs 2993 and 2996
remain draft pending those gates. No stopped preparation or controller restarted.
