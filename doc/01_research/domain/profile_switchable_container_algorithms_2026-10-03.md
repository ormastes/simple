# Item 7 primary-source research supplement

Reviewed 2026-10-03 through web search, without direct page fetching. The following are design inputs, not performance evidence for Simple.

## Plan legality before cost

[LLVM Vectorization Plan](https://llvm.org/docs/VectorizationPlan.html) separates legality constraints from cost-based alternative selection and includes retaining the original implementation as an alternative. Apply that separation to Simple's logical CollectionPlan and physical selector: a profile can rank legal candidates, but cannot establish equality purity, alias safety or duplicate/order equivalence. This is an application of the source's design principle, not a claim that LLVM supplies Simple's proofs.

[LLVM auto-vectorization](https://llvm.org/docs/Vectorizers.html) describes cost decisions and runtime checks. Simple should represent each emitted collection guard and its original-path fallback explicitly. A profitable common case cannot delete the fallback or evaluate a callback early to compute a guard.

## Storage contracts are observable

[Abseil container guidance](https://abseil.io/docs/cpp/guides/container) documents separate container families and their contracts. [Swiss Tables design notes](https://abseil.io/about/design/swisstables) describes metadata and probing costs. For Simple, candidate availability must include ownership/reference stability and memory costs rather than treating all hash storage as interchangeable. Collision/probe observations are useful cost evidence, but are neither a worst-case time proof nor a type-level equality proof.

## Consequences for acceptance

Compare contents and callback traces across physical choices, not only the chosen algorithm label. Include mutation during indexing, escaping element references, duplicate join keys, ordered iteration, early exit, and unsupported key capabilities. Measure build cost, lookup work, temporary bytes and materialization separately at geometric input sizes. Persist the exact source, target, workload and executable provenance with every result; external benchmarks cannot establish Simple's NFRs.
