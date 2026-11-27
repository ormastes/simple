# Smux resize revision: independent source review

Status: **WARN / NOT_RUN**. No scoped P0/P1/P2 findings remain. This is independent source review of the root-authored repair, not compiler, native, SSpec, or CoreMux admission. Eight cases are authored; zero were executed. No product sources were edited and no build, compiler, native helper, product, or test runner was launched.

Reviewed commit: `bae69fc813b6ca74c0449f92666e6d89c81647d1`, against `9ce3db18d9b7c61c80c4aba1447a7969afb0f019`; observed shared-tree HEAD: `9cb95a1552b289d6e804333c5e79a807dc3beeb6`. Scope excludes the configured PTY probe in that commit and concurrent RenameWindow work. All eight working-file hashes match the private v2 freeze exactly and their contents match the reviewed Git blobs after CRLF/LF normalization. The normalization comparison is separate from exact byte-hash verification.

## Source conclusions

- `service.spl:79` returns the existing record on exact dimensions. This preserves frozen capture state and avoids consuming an identity merely because a prior screen is dirty. Fresh records initialize their screen from the same pane dimensions.
- `window_layout_service.spl:106–122` checks every changed participant before any retained-grid resize. An exhausted identity returns an attributable error; no wrap, reset, saturation, or success-shaped unchanged result is introduced. Direct resize planning now has only this checked projection instead of an unchecked preliminary resize.
- `window_layout_service.spl:141–145` projects before native effects. Plans already carrying projected dimensions make this second projection a no-op. Native transaction admission at lines 224–246 checks the original records and all mappings/dimensions before capability lookup or the effect loop. A later exhausted participant cannot follow an earlier native resize through this path.
- Presentation and pane-removal callers propagate the new Result. Checked pane close retains the released target record and pending intent if projection fails; surviving ownership is not discarded. Existing native compensation and uncertainty handling remain intact.
- `split_checkpoint.spl:86–97` uses the same complete admission before record resizing. It operates on current records, preserving current output, input, focus, and cleanup authority rather than restoring saved pane contents. Refusal retains the split and added pane. This deliberately refuses compensation requiring a new identity when none remains; it does not claim native rollback succeeded.
- The bounded caller trace found the remaining record resizes in checked projection, checkpoint restoration after admission, and fresh split initialization. The separate terminal-shell backend resize is outside this retained-record owner. No mismatched Result caller was found in the scoped production and test call graph.

## Authored evidence and limits

The eight production-function controls cover exact no-op at MAX, exhausted pure projection, the last available identity followed by refusal, a later exhausted transaction participant, original-state transaction refusal, direct-plan refusal, border-plan refusal, and checkpoint refusal retaining the added pane. Their assertions check concrete revisions, dimensions, errors, and returned ownership counts; no synthetic native handles or fabricated effect counters are used.

The transaction cases cannot observe OS call ordering: both records are childless. The last-identity case exercises planning, not the final commit projection; the rollback case does not supply fresh output/input or native cleanup handles. Same-size frozen capture preservation is established by the early return source path, not a dedicated executed assertion. Compilation, actual value semantics, real viewport/compensation observations, screen stability, cleanup, and existing presentation/lifecycle suites remain pending under an admitted producer. Manual text is source-authored, not generator-qualified.

This report supersedes the older local report's statement that independent review was unavailable. Historical bug-report paragraphs describing four cases or incomplete pure containment describe earlier preparation; the current frozen spec contains eight cases and the reviewed checked projection. The bug remains OPEN for executable evidence.

## Exact input pins

Private manifest `build/review/smux-resize-revision-source-v2.sdn`: `5051f3484e25e79f3e8438387ec0b89b4c81dc80fb787cb6c19d96fe61360cc8`.

| Path | SHA256 |
| --- | --- |
| src/os/apps/smux/window_layout_service.spl | `2e71b7beb0e02b6d9d172ba35e9bf69ad1cd0d9428c2ecf97b50cba9ddab47b8` |
| src/os/apps/smux/service.spl | `8e6dfe9284dbf509cfcf57253c57eb8813d0b8ea096ccb1921c78ca27fb5f50d` |
| src/os/apps/smux/pane_presentation_service.spl | `91b9e1b7b6583146627e1464df001d1a42b26670c2183275343c1934dca064ce` |
| src/os/apps/smux/pane_lifecycle.spl | `a2c9d924ff1982c5af791b7fe7e1152bd4c805b0afcc717f6d7d74213c15da9c` |
| test/01_unit/os/apps/smux/resize_revision_admission_spec.spl | `67a4a9b4f12c16fda407897663658120dd12878867732aff52db31a6134b2609` |
| doc/06_spec/01_unit/os/apps/smux/resize_revision_admission_spec.md | `41a187245ebc9e7020264ccd9394986645af7e3be2ed96e0049c5b1d9c908423` |
| doc/08_tracking/bug/smux_resize_content_revision_exhaustion_2026-10-26.md | `2460e9831bf196c57f97334dfc9af5e0c0d833f0ef4acf0174d92c6f4a5a5b8a` |
| doc/09_report/smux_resize_revision_source_review_2026_10_26.md | `1a5efb7fe5d8e81cbf95670affad17d5dbc52703a8130db6388891b1c2bbad26` |
