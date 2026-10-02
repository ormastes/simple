<!-- codex-research -->
# Collection planning: domain research

Status: primary-source review, 2026-09-27. This extends the prior local plan
without importing external behavior as proof of Simple implementation.

- [Stream Fusion (Coutts et al., ICFP 2007)](https://www.cs.tufts.edu/~nr/cs257/archive/duncan-coutts/stream-fusion.pdf)
  shows how producer/consumer composition can remove intermediate sequences.
  A fused filter/map still scans linearly per input operation; it does not
  turn nested membership into an index lookup.
- [System R access path selection (Selinger et al., 1979)](https://web.stanford.edu/class/cs346/2014/selinger.pdf),
  [SQLite's query planner](https://www.sqlite.org/queryplanner.html) and
  [PostgreSQL's planner](https://www.postgresql.org/docs/current/planner-optimizer.html)
  support explicit candidate access paths and cost estimates. A Simple plan
  needs input and output cardinality, key distribution, memory and build cost,
  plus a guarded fallback when estimates are weak.
- [LLVM memory effects](https://llvm.org/docs/LangRef.html) illustrates why
  unknown call effects must remain conservative. Memory facts alone cannot
  prove callback order, exceptions, suspension or allocation equivalence;
  Simple's rewrite legality must cover those semantics separately.
- [Apache Arrow's columnar format](https://arrow.apache.org/docs/format/Columnar.html)
  and [DuckDB's vectorized execution](https://duckdb.org/docs/lts/internals/vector)
  motivate contiguous numeric columns and batched scans. They do not prove
  Simple's current DataFrame is vectorized. Numeric kernels should be measured
  separately from hash join/index selection.
- [Polly](https://polly.llvm.org/) provides a precedent for dependence-aware
  affine loop transformations. Such transforms require stricter proofs than a
  generic collection callback and belong to the numeric path.

Design implication: keep logical operations, legality evidence, symbolic costs,
physical candidates and runtime measurements distinct. Default to original
execution when any required proof is unavailable.

## 2026-10-03 primary-source update (Codex)

- [Polars lazy optimizations](https://docs.pola.rs/user-guide/lazy/optimizations/)
  separates predicate/projection pushdown, common-subplan reuse and join
  ordering. **Inference for Simple:** model each transformation separately.
  Eliminating repeated work requires an effect and alias proof because
  arbitrary Simple callbacks can mutate, throw or suspend. A relational
  optimization name is not such a proof.
- [DuckDB join operations](https://duckdb.org/docs/lts/guides/performance/join_operations)
  describes statistics-based cardinality estimation and configurable join
  ordering. **Inference for Simple:** compare build, probe and emitted-output
  work; include skew and all-equal keys. An all-matches join with n*m emitted
  pairs cannot satisfy a linear total-work claim even with a hash index.
- [Apache Arrow columnar format](https://arrow.apache.org/docs/format/Columnar.html)
  specifies a validity bitmap independently of value storage.
  **Inference for Simple:** a missing row and a present floating NaN remain
  different test cases. Preserve the explicit mask through typed/dynamic
  round trips; do not use a payload sentinel as the missing-value contract.
- [Polars explain API](https://docs.pola.rs/docs/python/dev/reference/lazyframe/api/polars.LazyFrame.explain.html)
  exposes plan inspection and optimizer controls. **Inference for Simple:**
  use receipts to explain alternatives and blockers, but pair them with
  compilation/execution evidence. A plan rendering is not evidence of
  executed lowering or improved scaling.

Sources reviewed through primary-site search on 2026-10-03; no third-party
summary establishes a Simple behavior. These findings refine verification of
already selected requirements rather than introducing relational SQL semantics
or additional optimization requirements.
