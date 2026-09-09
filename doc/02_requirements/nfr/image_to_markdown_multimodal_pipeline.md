<!-- codex-research -->
# Image-to-Markdown Multimodal Pipeline NFRs

Selection: N1 + C1 (approved 2026-09-08).

- NFR-001 Privacy: local endpoint is the default profile; remote egress requires an explicit profile setting. Never log secrets, raw image bytes, or data URLs.
- NFR-002 Limits: default decoded input limit is 20 MiB; bound pixels, tiles, queue depth, retries, request/response bytes, and tokens. One full-image request plus at most four uncertain-region retries by default.
- NFR-003 Time: default request timeout is 30 seconds with a configurable ceiling of 120 seconds.
- NFR-004 Proxy overhead: warm p95 preprocessing plus proxy overhead, excluding model inference and network time, is under 100 ms on the repository benchmark fixture.
- NFR-005 Structured reliability: at least 95% of responses on the acceptance corpus parse and validate without manual repair; failures remain explicit artifacts.
- NFR-006 Reproducibility: receipts record source/result hashes, dimensions, provider/model/revision, profile fingerprint, prompt/schema/preprocessing versions, timing, status, warnings, and observed-versus-inferred provenance.
- NFR-007 Compatibility: existing text-only Caret proxy/provider behavior remains covered and unchanged.
- NFR-008 Security: image/document content is untrusted data and cannot trigger tools, arbitrary URL fetches, filesystem reads, or provider fallback. File inputs must remain within explicitly permitted roots.
- NFR-009 Observability: record separate bounded timings for load/decode, preprocessing, transport, inference, validation, rendering, and cache lookup, plus retry and validation-failure counters.
- NFR-010 Evaluation: use checked-in synthetic/redacted fixtures plus a documented private-real-image evaluation recipe. Cover highlighted tables with Korean handwriting, single charts, multi-panel/multi-series charts, rotations, low contrast, log axes, overlap, missing legends, and malformed/oversized inputs.
- NFR-011 Accessibility/readability: Markdown remains understandable without opening JSON; uncertainty and unresolved content are visible in prose/table annotations.
- NFR-012 Resource behavior: no full-tree scans, repeated model discovery subprocesses, or repeated source rereads occur on the hot request path.
