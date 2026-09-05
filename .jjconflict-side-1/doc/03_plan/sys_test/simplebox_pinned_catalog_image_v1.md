# Simplebox pinned catalog image v1 test plan

- AC-01: decode the manifest only from exact canonical on-image SAM1 bytes.
- AC-02: bind SCR1, SAM1 identity, typed manifest, payload digest, target, and
  boot-owned trusted signer set before mutation.
- AC-03: reject truncation, trailing data, noncanonical fields, oversized
  values, payload substitution, and duplicate or malformed roots.
- AC-04: expose no public trust initialization, catalog session, ingestion, or
  loader-authority surface.
- AC-05: pass accepted data only to the existing loader-package signed catalog
  ingestion bridge.

The unit specifications are static handoff artifacts in this lane. No tests,
builds, SPipe execution, bootstrap, benchmark, optimizer, or verification were
run by instruction.
