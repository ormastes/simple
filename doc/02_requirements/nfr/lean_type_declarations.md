# Lean declaration NFR evidence plan

Determinism: identical MIR tables in different insertion orders must yield byte-identical module output. Sort source names and choose the first ready declaration; preserve original field/variant order. Sort symbol keys before declaration validation for stable diagnostics.

Memory: no process-wide cache or retained cross-module registry. Context/plans are module-local and proportional to symbols, dependency edges and generated source. The existing value-semantics allocator/copy behavior is not measured by source review.

Complexity: the straightforward deterministic topological selection costs O(V² + V·E) in the worst case, plus name-collision/member-duplicate checks and recursive type traversal; no linear-time claim is made. Existing text builder allocation behavior is inherited. Large-module latency/RSS and allocation measurement remain UNRUN. If these regress materially, file a concrete performance issue before acceptance.

Runtime gates: qualified Simple compiler execution of both SSpec files, generated Lean type checking with admitted Lean/Mathlib versions, and required compiler/lib/MCP/LSP smoke checks belong to root verification. No 80% branch-coverage, native-layout safety or runtime PASS claim is made from authored tests.
