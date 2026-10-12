# Filter selectivity shared-capture follow-up — 2026-10-10

This addendum records the implemented filter-selectivity slice for item 7. The
earlier inventory at `collection_capture_remaining_metrics_2026-10-03.md`
described the shared-channel blocker before this change; it remains a valid
description of that earlier state.

`adaptive_set_filter_observed` now sends its completed raw `evaluated` and
`accepted` counts to the process-scoped capture owner after successful
predicate evaluation and result materialization. Failed predicates, empty
inputs, and failed result materialization do not send a filter event. The
existing source site and target identity are forwarded unchanged. If optional
capture rejects the event, the capture owner marks the session failed and
`finish` reports failure; the completed filter still returns its business
result and caller-owned observation.

The shared owner validates `evaluated >= 0` and
`0 <= accepted <= evaluated`, aggregates both raw counters under the existing
capture lock with overflow checks, and treats `0/0` as unmeasured. At finish,
it emits one `filter_selectivity` metric per observed site as
`floor(total_accepted * 1,000,000 / total_evaluated)`. The calculation avoids
intermediate integer overflow. All-reject input emits zero; all-accept emits
1,000,000. Calls at one site are weighted by their actual evaluated counts.

The runtime tracks the aggregate `.sprof` row budget. A site consumes one
collection row and four baseline metrics; observed hash probes add two rows,
and observed filter selectivity adds one. The 100,000-row limit is checked
before accepting an event that would exceed it. The separate 14,285-site bound
remains unchanged. Core-C and Rust-provider runtime builds include the same
shared implementation. The interpreter adapter and existing runtime ABI
signature registries expose the new four-integer event.

The bounded core-C selfcheck passed on Ubuntu WSL. It covered weighted
aggregation, empty and invalid count pairs, count overflow, exact serialization
at 100,000 rows, and rejection beyond the cap. The new Simple capture scenario
is authored but remains unrun. It checks weighted aggregation, all-reject
zero, empty and predicate-failure omission, and preservation of the successful
filter result when capture rejects an invalid site.

This change measures only calls through `adaptive_set_filter_observed`; it does
not instrument all collection filters or compiler-generated filters. Loop-trip,
join-output, allocation-byte, and early-exit observations remain unimplemented.
