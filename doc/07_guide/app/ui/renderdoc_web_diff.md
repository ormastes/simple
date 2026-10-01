# RenderDoc web-renderer diff

Compares a RenderDoc capture of the **Simple Vulkan web renderer** against one of
**Chrome rendering the same catalog page** Vulkan-backed, and emits a structured diff
that a rendering-fix agent can act on.

## Contract

`scripts/tool/renderdoc-export-events.shs <capture.rdc> [--thumbs]` writes
`<capture>.events.json`, schema `renderdoc-events/v1`. Per event: `eventId`, `name`,
`type` (draw/dispatch/copy/clear/present), `pipeline`, vs/ps/cs hashes, `viewport`,
`scissor`, `targets[]` (id + width + height + format), draw params
(`vertexCount`/`instanceCount`, or `groupsX/Y/Z`), and `outputSha256` — sha256 of the
bound colour target saved as 8-bit RGBA PNG right after the event. `--thumbs` adds a
64×64 **raw RGBA8** downsample as base64 (`thumbFormat: "rgba8-64x64"`), raw rather than
PNG so the pure-Simple consumer needs no PNG decoder. The diff decodes that base64 and
compares whole 4-byte pixels (`src/app/ui/renderdoc_diff/thumb.spl`); `thumb_mismatch_pct`
is a real pixel percentage, not a base64-text proxy, and is `-1` when either side has no
thumbnail. Fixture thumbnails are 2×2 so the expected percentages are hand-checkable.

Shader "hashes" are the replay API's stage index plus entry-point name, not a content
digest: equal values do NOT prove equal shader bytes. They are informational only and no
classification reads them.

Fail-closed: bad `RDOC` magic → exit 1 (checked FIRST, so it works with no RenderDoc);
no `renderdoccmd`/`qrenderdoc` → exit 2 with `renderdoc_status=blocked:renderdoccmd-missing`.

The RenderDoc replay API is Python-only, so the **only** Python is the thin exporter
`scripts/tool/renderdoc-qrenderdoc-python-smoke.py` — extended in place, not duplicated;
with `RDOC_EXPORT_RDC` unset it keeps its original smoke behaviour. All logic (alignment,
classification, verdicts) is pure Simple in `src/app/ui/renderdoc_diff/`.

## Alignment rule

Three passes, per event-type bucket, in side-A order, never across types:

1. exact signature — type | pipeline | target WxH+format | draw params | name;
2. relaxed — render-target dimensions + format only;
3. ordinal pairing, **only when the unmatched remainders are equal in size**. Unequal
   remainders are not paired: leftover A events are `missing-draw`, leftover B events
   `extra-draw`. Without that guard one dropped draw shifts every later pairing and the
   gate names the wrong event id.

A matched pair is classified, first match wins: ordinal differs → `order`; dims differ →
`size-mismatch`; format differs → `format-mismatch`; output sha differs →
`output-mismatch`. `first divergent` is the lowest event id over all divergences.

## Running it

```bash
bin/simple run src/app/ui/renderdoc_diff/main.spl a.events.json b.events.json --out build/rdoc
sh scripts/check/check-renderdoc-web-diff.shs --selftest                 # 10 fixtures, fatal
sh scripts/check/check-renderdoc-web-diff.shs --capture-a chrome.rdc --capture-b simple.rdc
```

Keys: `renderdoc_diff_status=pass|fail|blocked:<reason>`, `renderdoc_diff_aligned=`,
`renderdoc_diff_divergent=`, `renderdoc_diff_first_divergent=`, `renderdoc_diff_report=`.
Verdict is the last stdout line: `RENDERDOC DIFF: PASS|FAIL|ERROR`; 0 events on either
side is ERROR, never a pass. Wired as bootstrap-tier row `renderdoc-web-diff` in
`config/check/must_check_gates.sdn`.

## Linux resume commands

```bash
sh scripts/setup/build-renderdoc-linux-vulkan-only.shs
sh scripts/tool/renderdoc-evidence.shs capture-html      # Chrome, Vulkan-backed  -> side A
sh scripts/tool/renderdoc-evidence.shs capture-simple    # Simple web renderer    -> side B
sh scripts/check/check-renderdoc-web-diff.shs --thumbs \
    --capture-a build/renderdoc/evidence/html/*.rdc \
    --capture-b build/renderdoc/evidence/simple/*.rdc
```

## Honest macOS status

This host has no RenderDoc, so **the replay half of the exporter has never executed**:
its RenderDoc API calls are written but unverified, and version renames are the likely
first failure. Everything else is proven here — the magic check, the missing-binary path,
the schema, and the whole diff — by `--selftest` over hand-written fixtures in
`test/fixtures/renderdoc_diff/`, which need no `.rdc`.

A binary that cannot `run` (a bootstrap-only CLI) is detected by a liveness probe and
reported as `blocked:simple-binary-cannot-run`, exit 2 — never as a FAIL.

Seed note: run specs with `SIMPLE_SEED=src/compiler_rust/target/bootstrap/simple`. That
seed renders `"${x}"` interpolation with a stray leading `$` and its `json_parse` returns
null for a plain object, which is why this lane concatenates with `+` and carries its own
flat JSON reader. Both are filed in
`doc/08_tracking/bug/seed_sep05_interpolation_dollar_and_json_parse_null_2026-09-12.md`.

`doc/07_guide/app/ui/` now holds 14 files against the ≤10-per-directory rule; it was
already over (12) before this guide landed, so the split is a separate cleanup.
