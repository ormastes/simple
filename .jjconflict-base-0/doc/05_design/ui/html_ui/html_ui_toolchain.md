# HTML UI Toolchain — Detail Design

State: `.spipe/html_ui_toolchain/state.md` (AC-1..9).
Research: `doc/01_research/ui/html_ui/css_theme_candidates_2026-06-12.md`,
`doc/01_research/ui/html_ui/smf_ui_builder_internals_2026-06-12.md`.

## Selection
Two CLIs (`ui_edit`, `ui_build`) over one shared core lib
(`std.common.ui.html_ui`), artifacts emitted as real SMF via
`bin/simple compile <gen.spl> --emit-smf -o out.smf` (minimal SMF = 179 B, so
< 4096 B dyn parts are real SMFs — no custom blob format; pending decision P1
resolved).

## Components
| Component | Path | Role |
|-----------|------|------|
| catalog | `src/lib/common/ui/html_ui/catalog.spl` | primitive element catalog (tag, WidgetKind mapping, tui_degrade note) |
| pair | `src/lib/common/ui/html_ui/pair.spl` | HtmlCssPair: html path + N css paths discovered from `<link rel="stylesheet">`; load/save/add_css/set_css |
| doc_ops | `src/lib/common/ui/html_ui/doc_ops.spl` | parse/serialize via `std.html_parser_utils`; list_elements, add_element, used_tags |
| payload | `src/lib/common/ui/html_ui/payload.spl` | base64 payload encode/decode, part split, element→part map, .spl codegen for main/part modules |
| dynsmf entry | `src/lib/common/ui/html_ui/dynsmf_entry.spl` | the background-built UI lib module (id `ui_html`) |
| ui_edit | `src/app/ui_edit/main.spl` + helpers | new/list/add-element/add-css/set-css |
| ui_build | `src/app/ui_build/main.spl` + helpers | build (std/dyn/merge) + --verify oracle |
| theme | `src/lib/common/ui/theme_html/{simple_default.css, theme_showcase.html}` | classless theme (Sakura-inspired, original CSS) covering full catalog |
| guide | `doc/07_guide/ui/html_ui/llm_html_ui_guide.md` | LLM authoring guide |

## Data Structures
- `HtmlCssPair { html_path: text, css_paths: [text] }`
- `UiCatalogEntry { tag: text, widget_kind: text, tui_note: text }`
- `UiBuildManifest` (sidecar `<name>.uib.sdn` next to artifacts):
  artifacts (path, role main|part, byte_count), element→artifact map,
  source html/css paths, form (std|dyn|merged), catalog elements implemented.
- Generated module exports: `ui_name() -> text`, `ui_elements() -> [text]`,
  `ui_html_b64() -> text`, `ui_css_b64(idx) -> text`,
  dyn main adds `ui_part_for(tag) -> text` (part artifact filename or "" when merged).

## Algorithms
### Build (`ui_build build page.html -o build/dynsmf/ui/ --form=std|dyn`)
1. Load pair, collect used tags; fail if a tag ∉ catalog.
2. `std`: codegen ONE module embedding html+all css as base64 consts +
   runtime parse helpers importing `std.html_parser_utils`; compile to one SMF.
3. `dyn`: codegen merged data-only module (no parser import) → compile; if
   SMF ≤ 4096 B → done, single main file (merge rule). Else split css/html
   payload into part modules sized so each part SMF < 4096 B (re-compile,
   shrink chunk on overflow, retry ≤ 8); main module embeds element→part map
   + primitive helpers only.
4. Write `UiBuildManifest` sidecar; print artifact list + sizes.

### Verify (`ui_build --verify <name>.uib.sdn` or dir)
1. Each artifact: file exists, byte_count ≥ 179, first 4 bytes == `SMF\0`
   (same contract as `DynSmfArtifactStatus`); dyn parts also < 4096 B.
2. Element coverage: every used tag of the recorded source HTML is in
   catalog AND mapped in manifest; report `OK <tag>` / `MISSING <tag>` lines.
3. Exit 0 only when all checks pass — this is the LLM parse/coverage oracle.

### Background build (AC-5)
Add `ui_html` to `dynsmf_default_manifest()` and
`dynsmf_manifest_source_path()` (`src/os/smf/dynsmf_session.spl:67-92`),
source = `src/lib/common/ui/html_ui/dynsmf_entry.spl`, output =
`build/dynsmf/ui_html.smf`; existing startup queue + check script handle the rest.

## Failure Handling
- CSS/HTML payloads MUST be base64 in generated `.spl` — `{}` in raw string
  literals triggers Simple brace interpolation (known repo gotcha).
- Part-split convergence failure (payload chunk < 256 B still > 4096 B SMF) →
  hard error with measured sizes, never silent oversize parts.
- `--verify` is fail-closed: unreadable sidecar or missing artifact = nonzero.

## TUI subset (guide content, no code this phase)
CSS degrades on TUI: colors→nearest 256, px→cells (8px≈1 cell), border-radius/
shadow/transition ignored, flex column/row honored, grid unsupported.

## Implementation Order
T1 core lib → {T2 ui_edit, T3 ui_build, T5 lane} → specs → review.
