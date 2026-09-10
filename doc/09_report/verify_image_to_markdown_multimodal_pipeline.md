# Verification Report: Image-to-Markdown multimodal pipeline

Date: 2026-09-08

- PASS — Research, selected requirements, architecture, detail design, system
  plan, executable system spec, manual, guide, and `image-read` skill exist.
- PASS — Feature source contains no `pass_todo`, vacuous assertions, TODO/FIXME
  markers, or executable specs under `doc/06_spec`.
- PASS — Numbered-artifact guards passed for working and staged paths: 674
  working paths classified, zero violations; zero staged violations.
- PASS — Staged direct-env/runtime guard passed.
- PASS — Two synthetic project fixtures have independent expected-content and
  SHA-256 records under `test/fixture/image_to_markdown/`.
- PASS — Astra's final scoped source/design review accepted receipt redaction,
  pre-dispatch request counting, validation-failure classification, retained
  failure timings, and the receipt-last hash-admission contract.
- PASS — Static coverage now includes typed timeout/truncation propagation and
  corrupted-cache rejection. Obsolete standalone inventory/extract/audit prompt
  helpers were removed so the test surface matches the single-request protocol.
- PASS — In the clean PR integration worktree rebased onto
  `origin/main@ff2431632dc4cbefa5484727bcb6518d38fc1abc`, both
  `direct-env-runtime-guard.shs --working` and `--staged` report `STATUS: PASS`.
- FAIL — No authoritative Simple compile/test result exists. A fresh three-cycle
  audit fixed backend diagnostic collection and two staged module-surface
  dictionary-boundary failures. The final `v6` candidate completed surface
  freeze through MIR, then hello-world AOT again failed with opaque
  `backend object-path status 1`. Evidence and the next scalar-diagnostic step
  are recorded in
  `doc/08_tracking/bug/bootstrap_stage2_backend_object_path_status_2026-09-08.md`.
  The only `bin/release/aarch64-unknown-linux-gnu/simple` currently present
  identifies itself as the Rust bootstrap seed and explicitly refuses normal
  tool status, so it is not valid substitute evidence.
- FAIL — NFR-004 warm p95/RSS evidence and NFR-005 acceptance-corpus structured
  reliability evidence cannot be produced until an admitted self-hosted runtime
  is available.
- WARN — Astra final review found that the native HTTP v2 client rejects HTTPS.
  The image adapter now routes HTTPS through the existing certificate-verifying
  browser H1/TLS stack with a single-hop aggregate deadline, while retaining
  HTTP v2 for admitted loopback Slang. This source fix awaits executable proof.
- WARN — `src/app/spipe/main.spl` remains owned by another active lane, so the
  image action stays a standalone SPipe entrypoint. It now optionally publishes
  the source/Markdown/JSON/receipt evidence binding via `--spec`; integration
  remains source-only until an admitted runtime can execute it.
- WARN — Astra's proxy/decoder audit led to source fixes for strict loopback
  authority parsing, profile image/pixel caps, bounded table/chart structures,
  timeout classification, bounded wire dispatch, and rejection of missing
  numeric chart fields. These edits are source-reviewed but cannot be compiled
  against an admitted runtime in this session.
- WARN — Astra's final delta audit additionally led to non-2xx rejection,
  deadline-error classification, strict lossless Base64 decoding, complete PNG
  chunk/CRC framing checks, smaller table complexity limits, strict scalar
  field types, chart-presence invariants, and inventory identity checks. These
  edits also await executable proof.
- WARN — Local admission now supports byte-identified PNG, JPEG, and WebP with
  bounded dimension parsing. Astra's follow-up rejected metadata-only positive
  vectors; admission now requires PNG IDAT/IHDR validity, JPEG scan+EOI
  framing, and an image-bearing WebP chunk with bounded chunk sizes. Exact
  Base64 padding is subtracted at the byte-limit boundary.
  The same inspector is now shared by the Caret proxy, eliminating its former
  PNG-only restriction. This remains source-only evidence.
- WARN — The extraction schema and Markdown projection now preserve explicit
  axis ranges, tick arrays, legend-to-series mappings, and annotation-to-point
  relationships. The inventory taxonomy was extended for scientific plots,
  chart subtypes, schematics, timelines, signatures/stamps, chemical/music
  notation, and barcode/QR regions. These additions await executable proof.
- WARN — The image-read skill validator passed before later documentation-only
  wording changes and was not rerun because each acceptance check is limited to
  one run per session.
- WARN — Receipt schema v3 now separates the safe error code from status and
  records request/cache state plus provenance-item and validation-check counts.
  The design and test plan now match the implemented single-call three-stage
  envelope. Static diff checks pass; executable proof remains blocked with the
  unavailable admitted runtime.
- WARN — Astra's receipt-v3 review found diagnostic leakage and an overstated
  multi-file atomicity claim. Failure receipts now retain only an allowlisted
  code and generic warning, request counts distinguish pre-dispatch rejection,
  elapsed provider-call time is retained, and the design specifies receipt-last
  hash validation as the publication admission boundary. Production-path
  counter assertions remain pending runtime execution.
- WARN — Astra's receipt follow-up found inaccurate pre-dispatch/error
  classification and discarded failure timings. The application now uses an
  explicit non-dispatch error allowlist, counts only schema/provenance failures
  as validation failures, carries measured phase timings into failure receipts,
  and returns only the safe error code rather than provider diagnostics.
- WARN — The call-plus-envelope-validation interval is recorded as an explicit
  `transport_ms` upper bound, while `inference_ms` remains zero. Exact transport
  and trusted provider-side inference timing remain an NFR-009 gap; the receipt
  no longer presents the aggregate as inference-only measurement.

STATUS: FAIL (2 failures, 11 warnings)
