# Flat pool decoders publish failed children

REQ-FLAT-POOL-TRUNCATION-001: A failed read must stop decoding before its value
or incomplete nested container is appended. Preserve complete children and the
reader's failure state in allocating and retained-destination decoders.

Status: source repaired; cached Stage 1 diagnostic PASS; self-hosted/native
qualification pending. This is a compiler cache correctness repair, not a
temporary workaround or a replacement for the compiler qualification gates.

The retained Phase 1 `flat_pool_codec_decode_cost_spec.spl` expected one complete
list from `2\n1\n7\n5\n`, but received two. The second nested child was appended
even though its reader had rejected its claimed five values. Current release
475c2f918db54a83cb30025fdf3610aea4cb2625 still contains that unguarded decoder.
Continuing after a failure also permits fabricated integer/boolean defaults.

All twelve pool decoder variants now check reader health before iteration and
before publishing each value. Scalar length preflight still rejects an entire
truncated scalar pool; nested pools retain only complete children. Complete and
empty lists keep their existing behavior. No encoded format or cache identity
is changed, and no cache was removed or compiler rebuilt.

Focused evidence under `build/phase1-flat-pool-truncation-20261011` binds the
release owner before/after SHA256 hashes and the cached bootstrap producer
15102d32226b3fbead63d3c63e33e99a6f0e9ffcddea06080fb65872445cbafb.
Source-inline diagnostics execute the real owner text plus the regression body;
they do not establish native import resolution or release admission.

- Release baseline: 13 executed, 7 passed, 6 failed.
- Repaired truncation scenarios: 13 executed, 13 passed, zero failed.
- Additional malformed canonical integer/boolean scenarios: 4 executed,
  4 passed, zero failed.

An initial scalar-prefix oracle was corrected after inspecting `next_len`'s
existing whole-scalar preflight; its expected result is empty with `ok=false`.
The original nested-list regression's one-complete-child oracle was preserved.

Regression owners are
`test/01_unit/compiler/frontend/flat_pool_truncation_spec.spl` and
`test/01_unit/compiler/frontend/flat_pool_canonical_failure_publication_spec.spl`.
Existing design: `doc/05_design/compiler/parsing/parser_architecture_unified_2026-02-04.md`.
No architecture or UI surface changes are needed.

Required next evidence: admitted self-hosted execution of these specs and the
compiler/core/MCP/LSP gates in AGENTS.md, followed by exact-head review and PR
integration into release/1.0. No release tag or publication is authorized here.
