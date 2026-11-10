# HTML/CSS rendering inventory lexical false pass

Status: OPEN — re-confirmed LIVE (partially addressed) 2026-11-11 (lane ne11), see addendum.

`scripts/check/check-html-css-rendering-manifest-traceability.shs:120-165` calls a tag/property rendered when its text appears in fixture HTML/CSS. It does not prove parsing, computed style, layout, Draw IR, device execution, or pixel effect. The checker’s CSS set also diverges from the 131-row executable inventory and contains claimed properties with no production owner.

Owner: web renderer inventory lane. Unblock: land `WebRenderableFeatureInventory`, classify tag/property/value-family rows honestly, bind renderable rows to production owners and focused readback evidence, generate the showcase from that inventory, and replace lexical promotion logic.


---

## 2026-11-11 addendum — lane ne11 (P3 traverse, batch ne11)

**Verdict: LIVE (partially addressed) — keep OPEN. The inventory landed; the
lexical gate it was meant to replace is still the wired gate.**

- **Landed:** `src/lib/gc_async_mut/gpu/browser_engine/web_renderable_feature_inventory.spl`
  (arrived with PR #7597 merge `9e7e7a526edb`, 2026-11-07) — typed
  fail-closed inventory whose header states "A row is never promoted by
  lexical occurrence in a fixture", with `renderable`/`partial`/`nonpaint`/
  `unsupported` classifications and `production_owner`/`test_owner` fields;
  the chrome showcase is generated from it
  (`src/app/ui/chrome_showcase/catalog.spl`, `main.spl`). Contract spec
  `test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderable_feature_inventory_contract_spec.spl`
  **13/13 PASS** (seed-smoke, fresh seed `46fe8f6b6def`).
- **Still LIVE:** `scripts/check/check-html-css-rendering-manifest-traceability.shs`
  still promotes by pure lexical occurrence — `has_html_tag` /
  `has_css_property` regex scans over fixture HTML/CSS blobs (read this lane,
  unchanged logic). Worse, that lexical checker is still invoked by three
  aggregate gates: `check-gui-renderdoc-feature-coverage-status.shs:979-1039`,
  `check-html-css-full-rendering-goal-status.shs:76`, and
  `check-html-css-renderdoc-goal-status.shs:91-94`. The "replace lexical
  promotion logic" half of the unblock is not done, so the false-pass class
  this record exists to stop still gates those reports.
- **Remaining work (owner: web renderer inventory lane):** rewire the three
  aggregate gates to consume `WebRenderableFeatureInventory` rows (renderable
  rows bound to production owners + focused readback evidence) instead of the
  lexical manifest check, then delete the lexical promotion block. Not taken
  on by this P3 lane: the rewired gates cannot be fully exercised here (their
  downstream Electron/bitmap evidence lanes do not run on this host), and
  landing an unverifiable gate replacement would repeat the false-evidence
  pattern this doc condemns.
