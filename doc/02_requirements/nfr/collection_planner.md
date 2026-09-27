<!-- codex-research -->
# Collection planner nonfunctional requirements

Selection: Option A, balanced production targets, chosen by the user on
2026-09-27. These targets apply to the full functional scope in
`doc/02_requirements/feature/collection_planner.md`.

- **NFR-001 Semantic parity.** Every selected physical plan must match the
  original program across the required engines for output, duplicate and
  missing-value behavior, order, callback count/order, exceptions, mutation,
  short-circuit and suspension. Unknown legality evidence selects the original
  execution path. Differential system fixtures and proof receipts verify this.
- **NFR-002 Indexed scaling.** Eligible equality workloads with 1,000, 2,000,
  4,000 and 8,000 input elements and bounded output multiplicity must have an
  operation-count scaling exponent at most 1.15. Count key equality, hash,
  comparison, index build/probe and emitted rows. Compute the exponent from the
  endpoint counts as `log(count_8000 / count_1000) / log(8)`; retain all four
  counts to expose irregular behavior. All-equal join fixtures separately
  account for their unavoidable output cardinality.
- **NFR-003 Runtime regression.** On representative eligible and fallback
  fixtures, no case may regress more than 10% in wall time relative to the
  same-revision unoptimized baseline. Use the same machine, target, backend,
  fixture and build flags, with at least five measured warm runs per case;
  compare medians. Preserve the raw samples in the verification evidence.
- **NFR-004 Memory regression.** Peak RSS for each representative fixture may
  be at most 20% above its same-revision unoptimized baseline. Record peak RSS
  per run and compare the median of at least five warm runs. Candidate
  selection must reject a plan whose estimated memory exceeds the configured
  cap before MIR lowering.
- **NFR-005 Compiler responsiveness.** Warm compiler startup and a
  representative collection-analysis request must each remain within 5% of
  their same-revision baseline median. Measure cold startup too, even though
  it has no numeric gate in this profile. Hot request handling must not repeat
  full-tree scans, file reads, process launches or retry sleeps.
- **NFR-006 Bounded planning.** Registry validation occurs once at startup or
  cache load. Resolved-symbol lookup is constant time on average, logical
  extraction is linear in the visited typed HIR nodes, and physical candidate
  enumeration has a fixed per-node bound. Cache keys include function and
  callee-summary hashes, registry version, target/backend capability, policy
  version and profile epoch; changing a component invalidates affected plans.
- **NFR-007 Explainability and reproducibility.** Each choice records the
  original and selected complexity, estimated build/probe/output work, memory,
  legality witnesses, rejected alternatives, profile identity and fallback
  reason. Replaying the same source, registry, target, backend and admitted
  profile must select the same plan. Tests must inspect these receipts rather
  than infer a plan solely from timing.

The performance gates apply only after NFR-001 parity and the corresponding
functional requirement pass. Missing or invalid profile data cannot relax a
legality requirement. The system test plan and generated SPipe manual must
report each measurement, baseline and verdict per backend.
