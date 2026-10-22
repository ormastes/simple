# HTML/CSS corpus integrity

**Source:** `test/03_system/app/ui/feature/html_css_corpus_integrity_spec.spl`

**Status:** Asset bytes audited on 2026-09-26; Simple scenario execution pending a current self-hosted runtime.

## Scenario: load the pinned rendering inputs

1. Parse the corpus manifest and require `simple-render-corpus/v1`.
2. For each of 48 original HTML cases, check its expected path, SHA-256,
   viewport, DPR and explicit `not-run` Simple/Vulkan status.
3. For the eight independent reference pages, check the matching path and
   SHA-256; require `independent-reftest` provenance.
4. Check the local checker SVG path and SHA-256.
5. Check the declared scroll and frozen-animation states in the relevant cases.

The scenario checks inputs only. It does not navigate the pages, render a frame,
verify fonts, compare pixels, or approve a Vulkan golden. Captured images and
interaction evidence belong to later renderer scenarios after a selected NFR
profile provides an admitted environment.

**Current evidence:** A read-only asset audit matched 48 source hashes, eight
reference hashes and one SVG hash. The Simple spec was attempted but stopped
before execution by an unrelated parser error in
`src/lib/nogc_sync_mut/io/process_ops.spl`.
