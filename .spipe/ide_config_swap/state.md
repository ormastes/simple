# Lane CFG4 — IDE call-site swap to std.config

Closes the roadmap row "IDE call-site swap to std.config" (blocked) left open after
CFG2 (editor config/platform/keybindings core swap) and CFG3 (test_runner swap).

Core under test: `src/lib/common/config_core/{schema,layers}.spl`.

## 1. Survey — every configuration read in `src/lib/editor/**`

Method: `grep` over `src/lib/editor/**/*.spl` for default tables, `if/else`
fallback chains, `file_read`, env lookups, per-key `match`/`if` ladders, and
`*_schema` / `*_config` / `*_settings` symbols. 30 candidate files inspected.

| # | Site (file:line) | Shape | Verdict |
|---|---|---|---|
| 1 | `00.common/config.spl:62-179` | layered SDN loader | **already routed** (CFG2) — `editor_config_schema()` on `ConfigFieldDescriptor`, resolution via `config_resolve`/`config_resolve_valid` |
| 2 | `00.common/platform.spl:72-131` | get/set-by-key ladder | **already routed** (CFG2) |
| 3 | `00.common/keybindings.spl:66-107` | SDN line scan | **already routed** (CFG2) — `config_parse_layer`/`config_parse_line` |
| 4 | `00.common/settings_schema.spl:6-14` | `struct SettingDescriptor` (key/label/description/category/setting_type/default_value/enum_options/platform) | **CONVERT** — strict subset of `ConfigFieldDescriptor` (only `setting_type` vs `value_type` differs). Duplicate type. |
| 5 | `00.common/settings_schema.spl:16-128` | 11 hand-written descriptor literals | **CONVERT** — key/type/default duplicate `editor_config_schema()` verbatim (all 10 defaults byte-identical). Second source of truth for defaults. |
| 6 | `00.common/settings_schema.spl:130-202` | 7 keybinding descriptor literals | **CONVERT** — label/description are a mechanical function of (key, command); 10 lines each. |
| 7 | `00.common/settings_schema.spl:204-266` | 6 platform descriptor literals | **CONVERT** — 4 of 6 duplicate `platform_config_schema()` defaults verbatim. |
| 8 | `00.common/settings_schema.spl:274-292` | `settings_filter_by_category`, `settings_filter_by_platform` | **CONVERT** — verbatim duplicates of `config_filter_by_category` / `config_filter_by_platform` already in `config_core/schema.spl:279-296`. |
| 9 | `00.common/settings_schema.spl:294-303` | `settings_search` | **CONVERT + LIFT** — generic over any descriptor list; belongs in the core. |
| 10 | `view/settings_view.spl:114-125` | `_settings_view_categories` + `_settings_view_contains` | **CONVERT** — distinct-category derivation + `config_contains_text` duplicate. |
| 11 | `view/settings_view.spl:97` | 8-field empty-descriptor literal | **CONVERT** — replace with core `config_empty_field()`. |
| 12 | `70.backend/gui_backend.spl:362-367` | `setting.setting_type` ladder | **CONVERT (rename)** — field rename to `.value_type`; the if/elif is a UI render switch, not config logic. |
| 13 | `core/workspace.spl:38-78` | `key = value` parse + get-with-default + serialise | **KEEP** — different on-disk format (`=` separator, `workspace "<path>"` header). Routing it through the `:`-only core parser would silently change the file format. Filed as a follow-up in §5, not converted. |
| 14 | `extensions/theme_manager.spl:29-43` | `theme_manager_color` fallback | **KEEP** — colour-table lookup, not layered config. |
| 15 | `core/launch.spl:11-80` | CLI argv parse | **KEEP** — argv is not a config layer in this design; no defaults table. |
| 16 | `services/file_watcher.spl:159-194` | ignore-glob defaults | **KEEP** — constants inside a matcher, no layering/merge. |
| 17 | `extensions/manifest.spl:57+` | extension manifest read | **KEEP** — package manifest, not user configuration. |
| 18 | `core/{recent,recovery,wal,document,session_db}.spl` | `file_read` of state/journal files | **KEEP** — persisted state, not configuration. |
| 19 | `services/{md,simple}_lsp_config.spl:10-21` | `LspClientConfig(...)` construction | **KEEP** — literal server-launch argv, no layering, no user override path. |
| 20 | `services/md_search.spl:343` | cache file read | **KEEP** — cache, not config. |
| 21 | `render/*`, `buffer/*`, `unified/*`, `extensions/builtin/*` | no config reads found | n/a |

Drift found by the survey (now recorded in code): `inlay_hint_refresh_delay_ms`,
`file_watcher_debounce_ms` and `file_watcher_ignore_globs` are declared by the UI
schema but by **no** loader schema, so nothing can actually resolve them. They are
kept as explicit UI-only descriptors and marked as such rather than silently
dropped.

## 2. Conversion

config_core additions (minimal, no local fork):
- `config_ui_field(...)` — full-metadata descriptor constructor.
- `config_with_ui(desc, label, description, category, enum_options, platform)` —
  decorate an existing loader descriptor with UI metadata, keeping its key, type,
  default and min/max. Promotes `value_type` to `"enum"` when options are given,
  which is exactly what the editor UI schema hard-coded for `theme`.
- `config_empty_field()` — the zero descriptor the settings view open-coded.
- `config_search(schema, query)` — lifted from `settings_search`.
- `config_categories(schema)` — lifted from `_settings_view_categories`.

Converted: sites 4-12 above. `settings_schema.spl` now derives every editor and
platform descriptor from `editor_config_schema()` / `platform_config_schema()`,
so the defaults exist once.

## 3. Specs
- New: `test/01_unit/lib/editor/settings_schema_config_spec.spl` — default
  resolution, override layer beats default, mandatory-as-ceiling clamp, and
  single-sourcing (UI default == loader default for every shared key).
- Regression: `test/01_unit/lib/common/config_core/config_layers_spec.spl` (was
  33 examples / 0 failures) and `test/01_unit/lib/test_runner/test_config_spec.spl`
  (10 / 0).
- Source-text specs asserting the old `SettingDescriptor` shape updated:
  `test/03_system/gui/editor_settings_{schema,platform}_spec.spl`,
  `test/system/editor_settings_{schema,platform}_spec.spl`,
  `test/03_system/.spipe_matchers_editor_settings_{schema,platform}_spec.spl`.

## 4. Results
See the lane report / the `config:` note line in
`doc/08_tracking/os/production_status.sdn`.

## 5. Follow-up (not done in this lane)
- `core/workspace.spl` uses a `key = value` document format. Routing it through
  config_core needs a separator-parameterised `config_parse_line`; deferred so
  this lane cannot change an on-disk format.
- `inlay_hint_refresh_delay_ms` has a live consumer
  (`src/app/editor/editor_controller.spl:2884`) but no loader entry — it is
  hard-coded to 300 there. Wiring it into `EditorConfig` is an app-layer change
  outside this lane's owned paths.
