# Backend variant-match workaround increases nested record copies

Bug: `backend_plugin_variant_match_copy_growth_2026_10_12`.
Canonical bug DB reconciliation is pending. Both optimization candidates
remain rejected; neither was applied to the shared source.

The current name-based enum workaround cannot be compared to the intended
direct enum equality under f2: the latter fails compilation. This experiment
compared two buildable alternatives under the same f2 producer and runtime.

Each real executable passed 48 semantic conditions and performed 500,000
iterations of three production membership calls. One name/match pair was
measured, followed by one changed inline-match candidate. No unchanged
baseline was replayed. The host was busy; these samples do not establish
general latency or percentile improvements.

| Variant | Process CPU seconds | Process peak working set bytes |
|---|---:|---:|
| Applied name equality | 1.031250 | 149057536 |
| Extra match helper | 0.671875 | 181264384 |
| Inline variant matches | 0.656250 | 181268480 |

Both candidates used less CPU in these samples, but peak working set rose
by roughly 32.2 MB, or 21.6 percent. They fail the no-memory-regression gate.

The emitted name-based membership code shallow-copies an 80-byte descriptor.
The match variants additionally load its offset 0x48 pointer and copy seven
eight-byte fields into a 56-byte allocation, matching the nested vtable.
Allocator rounding to 64 bytes over 500,000 calls is consistent with the
observed memory growth. The compiler decision causing this deeper copy is
not proven. Inlining did not remove it, refuting the first helper-boundary
hypothesis. This is not evidence of reading an enum as a 56-byte record.

The name methods call `rt_string_new_literal`; that runtime interns literals
and takes a global atomic-flag lock for lookups. Repeated literal allocation
on every name call was not established. Retaining the names workaround
therefore preserves the qualified behavior while the copy-policy issue is
investigated.

Evidence: `build/native_probe/backend-model-match-perf-20261012-astra/REVIEW.md`.
Review SHA-256:
`3562e22f23357abc69458e84e696e7669aba66adac2f08eef8db936c2631f781`.
Both experiment cycles are closed. A permanent producer repair must explain
copy depth, preserve value semantics and ownership, and verify behavior,
allocation volume, latency and peak memory before replacing this workaround.
