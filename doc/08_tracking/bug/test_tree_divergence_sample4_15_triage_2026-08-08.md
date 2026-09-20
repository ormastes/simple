# Test-tree divergence — sample 4 (15 pairs), triage report

Sampled the next 15 divergent pairs from `scripts/check/test_tree_divergence_baseline.txt`
using `awk 'NR%65==15'` — a residue class distinct from the three prior sessions'
samples (implicit first-15, offset 33/step 65, and `NR%65==50`). Cross-checked
against `doc/08_tracking/bug/test_tree_divergence_sample_15_triage_2026-08-08.md`
and the sample2/sample3 reports recovered from git history (commits
`45df29b8cba` and `21d9e850b88` — these two reports are not present in the
current working tree/HEAD, only reachable via those commits) to confirm zero
overlap. Also skipped `test/integration/app/app_mcp_intensive_spec.spl` per
instructions (not present in this sample anyway).

Convention: canonical = `test/01_unit/**` or `test/02_integration/**`; shadow =
`test/unit/**` or `test/integration/**`. All fixes below edit ONLY the shadow
copy to match canonical (verified canonical passes first), then run the
restored shadow with `bin/simple run <path>` (the deployed `bin/simple test`
hangs on this host for these specs, consistent with prior sessions' finding —
`run` was used as the fallback).

## Summary table

| # | Pair (label:relpath) | Classification | Verdict |
|---|---|---|---|
| 1 | `unit:compiler_core/entity/entity_structure_spec.spl` | **FIXED** — shadow was a vacuous 4-line stub, canonical has 2 real `it` blocks reading source files | canonical 2/2, shadow now 2/2 |
| 2 | `unit:lib/common/pure/pure_parser_phase1_2_spec.spl` | **FLAGGED — canonical itself broken** — canonical asserts a literal string (`if a.arg_kind == "option" and a.default_value.?:`) that no longer exists in `src/lib/nogc_async_mut/cli/simple_parser_api.spl` (refactored to `match a.default_value: Some(default_value):`); shadow is a vacuous 4-line stub | canonical 1/2 FAIL; shadow left as-is |
| 3 | `unit:app/lint_spec.spl` | **FIXED** — shadow had dropped 2 whole `describe` blocks (accessor/inherited-name checks, COLL006 string-concat rule) and weakened 2 assertions (`expect msg == ""` / `assert_true(... == "")` → `expect false`) | canonical 27/27, shadow now 27/27 |
| 4 | `unit:app/tooling/arg_parsing_spec.spl` | Cosmetic — `assert_true(x)` → `expect(x)`, identical semantics | left alone |
| 5 | `unit:browser_engine/margin_collapse_spec.spl` | Cosmetic — a `# @cover ...` doc-coverage annotation comment dropped | left alone |
| 6 | `unit:compiler/interpreter/mir_ssa_phi_intrinsic_spec.spl` | **FIXED** — shadow used equivalent `expect(err != nil).to_equal(false)` (kept, semantically identical to canonical's `to_be_nil()`) but was missing the final `it "returns the fail-closed sentinel for a never-written local"` block entirely | canonical 4/4, shadow now 4/4 |
| 7 | `unit:compiler/shb/shb_extractor_spec.spl` | **FIXED** — every real assertion in the shadow collapsed to `expect(true).to_equal(true)` (21 of 21 examples vacuous); the `shb_test_hash` helper and all string/hash assertions were stripped | canonical 21/21, shadow now 21/21 |
| 8 | `unit:lib/common/encoding/utf32_spec.spl` | **FIXED** — shadow was missing 2 edge-case `it` blocks (truncated LE/BE byte sequence → U+FFFD replacement) | canonical 24/24, shadow now 24/24 |
| 9 | `unit:lib/crypto/sha2_nist_vectors_spec.spl` | **FLAGGED — reversed pattern, canonical is the broken side** — canonical imports/calls `sha256_hex`/`sha512_hex`, which do not exist (`src/lib/crypto/sha256.spl` only re-exports `sha256_bytes`/`sha256_text`); canonical fails 6/8. Shadow already uses the correct `sha256_text`/`sha512_text` names and passes 8/8. Do NOT copy canonical over shadow here — that would reintroduce the break. Left both untouched; canonical needs a source-tracking human fix (rename `_hex`→`_text` in the 6 call sites), which is out of this triage's scope | canonical 2/8 pass (6 FAIL); shadow 8/8 PASS (unchanged) |
| 10 | `unit:lib/gpu/engine2d/cuda_session_contract_spec.spl` | **FIXED** — shadow had dropped 6 entire `it` blocks (injected FFI, quarantine-after-completion-unknown, generated-2D runtime provenance, typed launch evidence, bitmap glyph raster routing, readback evidence) plus 2 now-unused imports | canonical 10/10, shadow now 10/10 |
| 11 | `unit:lib/nogc_async_mut/websocket/websocket_facade_spec.spl` | **FIXED** — shadow had trimmed several imports (`bytes_to_text`, `sha1_rotate_left`, `word_to_bytes`, `extract_mask_key`) and dropped ~7 negative/edge-case assertions (negative base64 byte, SHA1 rotate overflow, invalid-byte-length payload, zero-chunk split, empty-mask, zero-length frame/extract cases) | canonical 1/1, shadow now 1/1 |
| 12 | `unit:os/crypto/scrypt_rfc7914_kat_spec.spl` | **FIXED** — shadow's 3 "deferred" `it` blocks (V2/V3/V4 documentation placeholders) were collapsed to `expect(true).to_equal(true)`, losing the documented hex-vector / byte-count assertions that make the deferral concrete | canonical 5/5, shadow now 5/5 |
| 13 | `unit:os/services/sched_service_spec.spl` | **FIXED** — shadow had weakened the id/generation assertion (`expect(e.id).to_equal(0)` + generation + `is_null()` → just `to_be_greater_than(0)`, which is actually WRONG given the documented id-0-is-valid regression) and dropped the entire "cross-entity identity (two-hop mutation-loss regression)" describe block (4 `it`s) documenting a real prior bug fix | canonical 12/12, shadow now 12/12 |
| 14 | `integration:rendering/pixel_verify_style.spl` | Cosmetic — one comment line differs (`--runtime-bundle core-c-bootstrap` vs `rust-hosted` in the build-command doc comment); no code difference | left alone |
| 15 | `integration:app/simple_lsp_mcp_stdio_spec.spl` | **FLAGGED — cannot verify in this environment** — canonical invokes `node bin/mcp_stdio_bridge.js -- bin/release/linux-x86_64/simple_lsp_mcp_server`, shadow invokes `bin/simple_lsp_mcp_server` directly; neither binary exists in this working tree (`bin/release/linux-x86_64/simple_lsp_mcp_server` and `bin/simple_lsp_mcp_server` both missing), so canonical cannot be run to confirm it passes before restoring. Shadow also drops a whole `it` ("swallows Claude and Gemini initialized notification before tools/list"), a helper fn, and 2 assertions — genuinely looks like the same vacuous-shrink pattern as the other 9 fixes, but restoring without a green canonical run would be unverified. Left shadow as-is | canonical/shadow both unrunnable here (missing MCP server binary) |

## Fixed (9 of 15)
1. `test/unit/compiler_core/entity/entity_structure_spec.spl`
2. `test/unit/app/lint_spec.spl`
3. `test/unit/compiler/interpreter/mir_ssa_phi_intrinsic_spec.spl`
4. `test/unit/compiler/shb/shb_extractor_spec.spl`
5. `test/unit/lib/common/encoding/utf32_spec.spl`
6. `test/unit/lib/gpu/engine2d/cuda_session_contract_spec.spl`
7. `test/unit/lib/nogc_async_mut/websocket/websocket_facade_spec.spl`
8. `test/unit/os/crypto/scrypt_rfc7914_kat_spec.spl`
9. `test/unit/os/services/sched_service_spec.spl`

Every fix was verified by running the restored shadow with
`bin/simple run <path>` (60-180s each) and confirming it matches canonical's
example count with 0 failures — not just that it parses.

## Flagged, not fixed (3 of 15)
- `test/unit/lib/common/pure/pure_parser_phase1_2_spec.spl` — canonical's
  assertion text is stale vs. current `simple_parser_api.spl` source (real
  API drift bug, needs a human decision on whether to update the assertion
  text or the source).
- `test/unit/lib/crypto/sha2_nist_vectors_spec.spl` — **reversed** case: the
  shadow is actually correct and the canonical is broken (`sha256_hex`/
  `sha512_hex` don't exist; should be `sha256_text`/`sha512_text`). Filed here
  rather than fixed because fixing the canonical is outside this triage's
  scope (shadow-vs-canonical reconciliation), but it's a real, easily
  fixable bug: `test/01_unit/lib/crypto/sha2_nist_vectors_spec.spl` lines
  16-17, 44, 49, 54, 71, 76, 81 call `sha256_hex`/`sha512_hex` — rename to
  `sha256_text`/`sha512_text` to match `src/lib/crypto/sha256.spl` /
  `sha512.spl`'s actual exports.
- `test/integration/app/simple_lsp_mcp_stdio_spec.spl` — cannot verify either
  side; the `simple_lsp_mcp_server` binary this integration spec drives is
  not built in this working tree.

## Cosmetic / legitimate, left alone (3 of 15)
- `test/unit/app/tooling/arg_parsing_spec.spl` — `assert_true` vs `expect`.
- `test/unit/browser_engine/margin_collapse_spec.spl` — dropped `@cover` doc
  comment.
- `test/integration/rendering/pixel_verify_style.spl` — one build-comment
  runtime-bundle name differs.

## Note on prior reports' availability
`doc/08_tracking/bug/test_tree_divergence_sample2_15_triage_2026-08-08.md` and
`..._sample3_15_triage_2026-08-08.md` (referenced in this task's instructions)
are **not present in the current working tree** — only `sample_15` (the first
report) exists on disk. The other two exist only in git history, in commits
`45df29b8cba` ("sample 2") and `21d9e850b88` ("sample 3"), neither of which is
an ancestor of the current HEAD (`1226a2064fb`). This matches the repo's known
shared-WC/clobber failure mode documented elsewhere in
`doc/08_tracking/bug/`. Their pair lists were recovered via `git show
<sha>:<path>` for the purpose of confirming this sample's non-overlap; no
attempt was made to restore those commits' actual file fixes into this
working tree (out of scope for this task).
