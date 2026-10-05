# Source snapshot performance options

<!-- codex-research -->
Status: OPTIONS; user selection pending. Tracking: TODO 347.

Existing code already reuses identical snapshots and scopes per-file scratch.
Do not implement those again. See the [local research](../../01_research/local/windows_source_snapshot_latency.md)
and [domain research](../../01_research/domain/windows_source_snapshot_latency.md).

| Option | Description | Pros | Cons | Estimated effort |
| --- | --- | --- | --- | --- |
| A: Existing-path optimization | Instrument and remove repeated manifest decode/validation work within one immutable request epoch; narrow only selectors whose completeness is proven | Smaller change; preserves existing authority; useful regardless of later design | Whole-family cold inventory remains; request caching needs lifetime and identity checks; fixture-only narrowing does not solve general imports | M, approximately 4–8 source/test files |
| B: Dependency-scoped immutable views | Integrate existing proposed semantic read-set/frozen-source design into production admission; reuse content-addressed bytes and materialize complete dependency closure | Reduces files copied and validated for small builds; best fit for low latency at scale | Must account for negative resolution, traits/impls, generated files, macros, selectors and configuration; broad correctness surface | L/XL, approximately 10–20 source/test files plus design updates |
| C: Research and measurement only | Instrument costs and produce controlled profiles before choosing a snapshot algorithm | Lowest semantic risk; stronger basis for prioritizing changes | Does not itself reduce user-visible latency | S/M, approximately 3–6 source/test files |

Recommendation: B as the intended design, preceded by measured A improvements
that do not conflict with it. This recommendation is not recorded as selection.
The active bootstrap remains unchanged and runs through Phase 4 under all options.

REQ-001: Preserve exact admitted source bytes and dependency invalidation.
REQ-002: Record files enumerated/hashed/copied, bytes and repeated manifest work.
REQ-003: Preserve truthful compile errors and actual output behavior.
REQ-004: Validate memory and logic for each performance change.
REQ-005: Keep active bootstrap generations immutable and preserve caches.

No acceptance claim follows from a small Hello snapshot alone: general imports,
negative candidates and source mutation cases must remain correct.
