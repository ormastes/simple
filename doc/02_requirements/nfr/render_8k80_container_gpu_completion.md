# Container/GPU 8K80 completion NFRs

- **NFR-R8KC-001 Performance:** p95 <=12.5 ms for each admitted damage class;
  warmup/sample count and measured scope are mandatory receipt fields.
- **NFR-R8KC-002 Provenance:** compiler, source, binary, workload, container
  image, GPU/device, driver, and receipt hashes must be retained.
- **NFR-R8KC-003 Isolation:** container execution is bounded by time, memory,
  CPU, dropped capabilities, no-new-privileges, and an explicit GPU set.
- **NFR-R8KC-004 Reliability:** parsers and aggregation fail closed; unavailable
  prerequisites exit blocked, while malformed or contradictory evidence fails.
- **NFR-R8KC-005 Reproducibility:** cached artifacts execute directly; raw
  source, interpreter, Rust seed, and silent fallback are inadmissible.
- **NFR-R8KC-006 Scope honesty:** headless/container evidence never claims
  physical connector, EDID, refresh, or captured-scanout proof.
