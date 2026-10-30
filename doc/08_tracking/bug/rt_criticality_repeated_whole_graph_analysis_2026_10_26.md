# RT criticality repeats whole-graph work per ordinary root

Status: source repair candidate; executable correctness, optimizer CLI and
paired p50/p95 wall/RSS qualification UNRUN. This is a concrete algorithmic
work duplication, not a sampled claim about the live Phase3 hotspot.

The retained frozen `83be` validator resolves each claim by scanning every
function. Each ordinary root then calls `rt_admit_with_capabilities_v1`, even
with an actually empty capability list: serialize/sort the complete graph for
its root-specific digest, copy every fact, rebuild the index and compute the
same unadjusted effect closure again. With R roots and V/E graph size this
repeats O(R*(V+E+graph serialization/sorting)) work and retains temporary owners.
CPU activity and the reported elapsed RT stage are not a profile or proof of
the proportion attributable to these operations.

The candidate indexes function names to ordered declaration indices, preserving
the existing exact module-key/path/name predicate and ambiguity sentinel. It
does not collapse aliases or change claim/diagnostic order. For ordinary roots
with exactly zero actual capabilities, a fresh invocation-local lazy analysis
computes the unadjusted closure once. Every nonempty list, including stale or
invalid capabilities, keeps the original digest-bound path. HAL synthetic
intrinsic construction and admission remain on their original separate route.
The input observer is not a reusable authority/cache: its fields are ignored
and only the observed graph-build count is written back. No global cache,
policy bypass, weaker unknown-call behavior or skipped inventory check exists.

Existing merge-sort and scoped blob streaming fixes are already present in
`83be`. PR4826 adds bounded progress only. The bounded target history check
found no equivalent shared empty-capability analysis repair.

`rt_criticality_shared_analysis_spec.spl` is executable SPipe coverage of actual
policy replay. A 1000-function/100-root case compares complete ordered severity
and messages against the unchanged nonempty-but-invalid grant route, expects
100 diagnostics and one real shared graph build. Additional cases cover
unknown/ambiguous roots, path aliases, lower-tier warnings, HAL-only separation,
matching capability digest and stale-digest refusal. These cases are authored
UNRUN, not a mathematical or executable proof of equivalence yet.

No qualified full self-hosted CLI is available for the baseline, optimizer or
SSpec route. No seed fallback, compiler/native build, live attachment, altered
environment or watchdog was used. Do not claim speedup, memory improvement or
optimization acceptance until real differential execution and paired p50/p95
and peak/steady RSS measurements satisfy the optimize skill's joint budgets.
Independent Astra source review is required before any source-only landing;
the active frozen compiler source and caches remain unchanged.
