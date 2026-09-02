# MBH-NFR-003 Baseline Receipt Schema

Status: SELECTED.

One immutable admitted receipt is required for each architecture:

```text
schema=macos-m4-residency-baseline-v1
status=ADMITTED
requirement_id=MBH-NFR-003
selection_policy=baseline-relative-10-percent
decision_source=user-final-performance-authority-2026-09-02
architecture=<arm64|x86_64>
request_count=20
baseline_rss_kib=<positive measured integer>
baseline_evidence_sha256=<64 lowercase hex characters>
producer_sha256=<64 lowercase hex characters>
server_sha256=<64 lowercase hex characters>
authority_document=doc/02_requirements/nfr/macos_bootstrap_reverse_reference_harmonization.md
authority_document_sha256=<64 lowercase hex characters>
```

The checker binds the receipt to the requested architecture and actual
producer-built server bytes. It derives the only selected limits: steady RSS is
baseline × 110%, and nonnegative growth across 20 warm requests is baseline ×
10%. Missing, template, duplicate, unknown, cross-architecture,
stale-document, or digest-mismatched receipts fail closed.
