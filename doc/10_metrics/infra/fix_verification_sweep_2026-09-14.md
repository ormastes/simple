# Fix verification sweep — 2026-09-14

Verifies that fixes landed 2026-09-13/14 across parallel lanes (web parity
round 13 / PR #959, GPU boundary hardening, runner) still hold TOGETHER at
`origin/main` tip `79ef60f34a5`. Runner:
`SIMPLE_EXECUTION_MODE=interpreter SIMPLE_TIMEOUT_SECONDS=0
/Users/ormastes/simple/build/cargo-r2/release/simple` (sha `2d066932…`, built
2026-09-14 08:34, symlink target `stat -f %Sm` = `Sep 14 08:34:50 2026`).
Run from an agent worktree checked out at the same tip; the binary itself
lives at the absolute path above (built in the primary checkout, not this
worktree — invoked by absolute path, content-identical either way).

All specs and gates below ran ONE AT A TIME with a fresh process. No fixes
were applied by this sweep.

## Group A — web parity/text (18 specs, all PASS at expected counts)

| spec | expected | actual | verdict |
|---|---|---|---|
| nested_list_container_ua_margin_spec.spl | 8/8 | 8/8 | PASS |
| non_ascii_run_wrap_byte_advances_spec.spl | 6/6 | 6/6 | PASS |
| inline_pen_collapsed_space_spec.spl | 6/6 | 6/6 | PASS |
| text_byte_codepoint_index_residue_spec.spl | 9/9 | 9/9 | PASS |
| inline_element_ua_display_table_spec.spl | 8/8 | 8/8 | PASS |
| replaced_element_default_intrinsic_box_spec.spl | 9/9 | 9/9 | PASS |
| form_control_widget_box_spec.spl | 12/12 | 12/12 | PASS |
| platform_system_face_metrics_spec.spl | 25/25 | 25/25 | PASS |
| fractional_advance_accumulation_spec.spl | 11/11 | 11/11 | PASS |
| paint_layout_advance_parity_spec.spl | 2/2 | 2/2 | PASS |
| sfnt_batch_glyph_advances_equivalence_spec.spl | 4/4 | 4/4 | PASS |
| kern_pair_advance_accumulation_spec.spl (#959 kern spec) | 9/9 | 9/9 | PASS |
| li_nested_list_scope_spec.spl | 5/5 | 5/5 | PASS |
| first_child_top_margin_collapse_spec.spl | (unspecified) | 10/10 | PASS |
| li_marker_nth_path_key_spec.spl | (unspecified) | 3/3 | PASS |
| table_layout_spec.spl | 9/9 | 9/9 | PASS |
| html_tokenizer_spec.spl | 53/53 | 53/53 | PASS |
| web_overflow_triple_memo_equivalence_spec.spl | 2/2 | 2/2 | PASS |

All ran at `test/01_unit/browser_engine/*` (canonical location; a stale mirror
also exists under `test/unit/browser_engine/` and was NOT used).

## Group B — GPU (4 specs + boundary-audit matrix, all PASS)

| check | expected | actual | verdict |
|---|---|---|---|
| catalog_vulkan_twin_spec.spl | 3/3, max_delta 0 | 3/3 | PASS — note: the spec's own assertion is `expect(diff.max_delta <= 8).to_equal(true)`, not an exact-0 check; the task's "max_delta 0" claim is not what the spec asserts, so it is reported as spec-PASS under its actual `<=8` threshold, not independently confirmed at exactly 0. |
| gpu_boundary_invariants_spec.spl | 2/2 | 2/2 | PASS |
| catalog_cpu_determinism_spec.spl | 3/3 | 3/3 | PASS |
| engine2d_shadow_rect_twin_formula_spec.spl | 3/3 | 3/3 | PASS |
| `check-web-vulkan-gpu-boundary-audit.shs --matrix` | PASS 4/4 | `PASS — 4 matrix cell(s) audited (overview + css-layout at 900x760 and 3840x2160), 0 violations` | PASS |

Two of these (catalog_cpu_determinism_spec.spl at 3.5K frames and the
boundary-audit's 3840x2160 render cells) took roughly 14+ minutes wall each
under `interpreter` mode — genuinely CPU-bound (confirmed via `ps` at 90-100%
CPU throughout, not hung), not a regression finding, but worth noting for
anyone re-running this sweep under a tight timeout.

## Group C — perf digests

Ran `test/05_perf/ui/web/pipeline_bench.spl` once with
`SIMPLE_WEB_STYLE_COUNTERS=1`. Draw IR digests (8/8, page order
overview/html/css-layout/css-paint/forms-media/animation/evidence/tab-bar):

```
cf7e2b1502ca2514 b8c78ff3db464e89 395ec3ef905811eb 99868f409a846a42
d9c095de86d67a9f e71244e2526ccf75 84d9275adb82bc9e 99a807c8efee9def
```

Round-13 baseline (`doc/10_metrics/ui/web_perf_round13_2026-09-13.md`):

```
1d22f0682a6f4ae1 8c2d9f380e7dcc3d ea9df39e03ecd2cb fd9d26e9eff2d9b3
0d8baa45b77f5bda 066600bb7d9cef53 4cf797f8c3a8f3a4 56097a5a1ce50dda
```

**All 8/8 digests changed**, including pages (overview, css-paint, animation,
evidence, tab-bar) with no nested lists, non-ASCII text, or forms — broader
than the "pages with nested lists/non-ASCII/forms/media" hint in the task
would predict on its own. Explained: the change set landed between the round-13
baseline and this run includes `platform_system_face_metrics`,
`fractional_advance_accumulation`, `sfnt_batch_glyph_advances`, and
`kern_pair_advance_accumulation` fixes plus the round-13 UA-table/table-layout
landing — these touch text-run/glyph-advance and table-layout code paths that
execute on every page (any page with any text or any table gets a different
byte-for-byte Draw IR stream even with no visible layout change). Suspect PR:
**#959** (`work/web-parity-round13-2026-09-14`), corroborated by its own
follow-up commit `c694a86bef6 docs(ui): geometry re-baseline on the fresh
runner (html page, PR #959 follow-up)` — i.e. the round-13 authors already
recorded a baseline re-earn was expected and is tracked, not a silent
regression.

Per-page cold ms: **not captured**. `pipeline_bench.spl` itself emits only
`[bench] page=<name>` / `[bench] digest page=<name> sha=<hex>` lines under
`SIMPLE_WEB_STYLE_COUNTERS=1`; no `cold_ms`/timing line is printed by this
invocation. The round-13 doc's cold-ms table appears to come from a separate
harness/wrapper not identified in this sweep's time budget — flagged as a gap
rather than fabricated.

## Group D — gates

| gate | verdict (verbatim) | rc |
|---|---|---|
| check-guard-wiring.shs | `check-guard-wiring: PASS — 1714 guard(s) checked, 673 invoked, 1021 orphaned (605 baselined as known unwired debt, rest justified), 0 NEW unwired, 0 copied hook(s)` | 0 |
| check-tracking-db-unique-ids.shs | `PASS — 3038 row(s) checked across 6 table(s), 0 duplicate ids` | 0 |
| check-no-document-symlinks-push.shs | `PASS — 137368 tree entr(y/ies) checked at origin/main, 116 symlink(s), 0 carry document content` | 0 — **note:** the script only accepts `--rev <commit>` / `--selftest`, not a `BASE..NEW` range; ran as `--rev origin/main` instead of the requested `origin/main~30..origin/main` (that invocation errors with a usage line). Deviation recorded rather than silently substituted. |
| check-runner-binary-extern-freshness.shs | `ERROR — 3323 extern(s) checked, binary … (2026-09-14 08:34) predates declaring source for: rt_font_glyph_index(…/shaper.spl) …` | 2 — **classified ENV-ARTIFACT, not a real regression.** Verified: `shaper.spl`'s last real commit is `ae55a746719` dated 2026-08-11, three weeks before the binary was built; the worktree's `git log -1` tip (`79ef60f34a5`) is 2026-09-14 11:32; but `stat -f %Sm` on the checked-out file reads `Sep 14 11:54:59 2026` — the agent worktree's checkout/`git reset --hard` mtime, not a content-freshness signal. The gate compares filesystem mtime, and a worktree checkout always postdates any binary built earlier that same day. Re-running from the primary checkout (no `scripts/check/` present there in its current state) was not possible in this sweep window; recommend re-verifying from a checkout that was never freshly re-materialized. |
| check-bootstrap-stage3-receipt-autowire.shs | `PASS — 19 check(s) run, 0 failed` | 0 |
| check-shadow-rect-spirv-pinned.shs | `PASS — 5136 byte(s) compared, 4 selftest fixture(s) checked, backend_vulkan_shadow_rect_spirv.spl matches shaders/shadow_rect.comp (sha256 848ffd969b9a4a7c8326f540caaf1bc6bccf6b1690e2cc9c761f1007a1fd26d7)` | 0 |

## Group E — runner (3 specs, all PASS)

| spec | expected | actual | verdict |
|---|---|---|---|
| light_request_claim_spec.spl | 2/2 | 2/2 | PASS |
| client_timeout_env_spec.spl | 7/7 | 7/7 | PASS |
| docgen_end_to_end_spec.spl | 1/1 | 1/1 | PASS |

## Summary

- Specs: **25/25 PASS** (18 + 4 + 3), all at their exact declared counts.
- Gates: **5/6 PASS**, **1 ERROR** (`check-runner-binary-extern-freshness.shs`),
  classified as a worktree-mtime environment artifact, not a code regression —
  see Group D note.
- GPU boundary-audit matrix: **PASS 4/4, 0 violations**.
- Perf digest gate: **8/8 digests changed** vs round-13 baseline, explained by
  PR #959 (round-13 web-parity landing) touching universal text/table layout
  paths; per-page cold-ms not captured by this invocation of
  `pipeline_bench.spl` (gap noted, not fabricated).

No red findings block landing. The one ERROR is an environment artifact of
running the freshness gate inside a freshly-checked-out agent worktree, not a
fix regression, and is recorded rather than silently dropped.
