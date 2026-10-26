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
