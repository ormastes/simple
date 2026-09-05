# Lane CFG2 — std.config call-site swap (P7 increment 2)

Status: **COMPLETE — editor consumes `std.common.config_core`; duplicate parser /
conversion / precedence logic deleted. Uncommitted, left in the working copy per
lane instructions.**
Date: 2026-07-27
Master plan: `doc/01_research/domain/simpleos_production_host_master_plan.md` §16
Predecessor: `.spipe/simpleos_harden_p7_config/state.md` (increment 1 — core extraction)

## Files changed

| File | Change |
|---|---|
| `src/lib/editor/00.common/config.spl` | rewritten on `config_core`; local parser + conversions + guards deleted; layered loader added |
| `src/lib/editor/00.common/platform.spl` | get/set ladder + per-key struct rebuild routed through `config_core`; `extern fn parse_int` deleted |
| `src/lib/editor/00.common/keybindings.spl` | document scanner deleted; `_kb_parse_line` routed through `config_parse_line` |
| `test/01_unit/lib/editor/config_core_migration_spec.spl` | new — behaviour-preservation spec |
| `.spipe/simpleos_harden_cfg2_callsite/state.md` | this file |

`src/lib/editor/00.common/settings_schema.spl` was **not** modified — see
"config_core follow-ups" below for why.

## Duplicates DELETED (file:line refer to the pre-change revision, `git show HEAD:<path>`)

1. **SDN document scanner, copy 1 of 3** — `config.spl:44-56` `_ec_apply_sdn`
   (13 lines). Now `config_parse_layer(content, layer)`.
2. **SDN line splitter, copy 1 of 3** — `config.spl:58-65` (the trim / `#` /
   find-`:` / slice-key / slice-value head of `_ec_apply_line`). Now
   `config_parse_line`.
3. **Per-field struct reconstruction** — `config.spl:66-94`: ten near-identical
   full `EditorConfig(...)` literals, one per key, ~200 chars each (29 lines).
   Replaced by ONE `EditorConfig(...)` literal in `editor_config_from_entries`.
4. **`_ec_find_char`** — `config.spl:96-102` (char scan). Duplicate of
   `layers.spl:_cfg_find_char`. Deleted, no local replacement.
5. **`_ec_parse_int`** — `config.spl:104-112`. Now `config_parse_int`.
6. **`_ec_bool_to_text`** — `config.spl:153-156`. Now `config_bool_to_text`.
7. **`_ec_int_to_text`** — `config.spl:158-167`. Now `config_int_to_text`.
8. **`_ec_digit_char`** — `config.spl:169-179` (11-arm digit ladder). Now
   `_cfg_digit_char` inside the core.
9. **Hand-built save serializer** — `config.spl:141-150` (ten string-concat
   lines). Now `config_entries_to_sdn(editor_config_to_entries(config, "user"))`,
   which emits byte-identical output.
10. **`extern fn parse_int`** — `platform.spl:50`. Second, *different* int parser
    in the same directory. Deleted; now `config_parse_int` +
    `config_is_int_text` validation via `config_resolve_valid`.
11. **Inline bool→text if/else** — `platform.spl:59-63`. Now `config_bool_to_text`.
12. **Per-key `PlatformConfig(...)` rebuild** — `platform.spl:69-122`: five
    full five-field struct literals, one per key (54 lines). Replaced by ONE
    literal in `platform_config_from_entries`.
13. **SDN document scanner, copy 3 of 3** — `keybindings.spl:62-80` (19 lines of
    char-scan + slice + trim + last-line handling inside
    `keybinding_config_load`). Now `config_parse_layer`.
14. **Line trim / separator split, copy 3** — `keybindings.spl:85-94`
    (`key_prefix` search + `key_start` slice). The `key: `/value split is now
    `config_parse_line`; only the binding-specific `command:` / `mode:`
    sub-field split remains local.

Total: **14 duplicate sites removed**, ~125 lines of duplicated logic. Net file
size is roughly flat because the swap also *adds* the ten-layer loader
(`editor_config_load_layers`), the typed schemas, and doc comments that did not
exist before.

## What now routes through config_core

`config.spl`
- `editor_config_schema() -> [ConfigFieldDescriptor]` — the ten `EditorConfig`
  fields as typed descriptors (`config_field` / `config_int_field`), carrying the
  minimums the old code open-coded (`font_size`/`tab_size`/`auto_save_delay_ms`
  min 1; `hover_delay_ms` min 0).
- `editor_config_from_entries(entries)` — resolve then build the struct once.
- `editor_config_load_layers([EditorConfigSource])` — **NEW capability**: reads
  any set of `(path, layer)` documents and resolves by layer RANK, so
  vendor / machine / sysadmin / device / profile / session / **mandatory** are
  now reachable from the IDE and a mandatory-policy document pins its keys even
  when a workspace or session document is read after it.
- `editor_config_load(user_path, workspace_path)` — signature UNCHANGED (it is
  asserted verbatim by `test/03_system/gui/editor_gui_spec.spl:90`); now a
  two-element call into `editor_config_load_layers`.
- `editor_config_to_entries(config, layer)` — snapshot for set/serialize.
- `editor_config_set_by_key` — "current config at `compiled_default` + one entry
  at `user`", then resolve. This is what deletes the ten struct literals.

`platform.spl`
- `platform_config_schema()`, `platform_config_to_entries`,
  `platform_config_from_entries`, `platform_from_name`.
- `platform_config_get_by_key` / `_set_by_key` signatures UNCHANGED (asserted
  verbatim by `test/03_system/gui/editor_settings_platform_spec.spl`).

`keybindings.spl`
- `keybinding_config_load` → `config_parse_layer`.
- `_kb_parse_line(line: text) -> KeyBinding` → `config_parse_line` +
  `_kb_binding_from_entry`. Signature UNCHANGED (asserted verbatim by
  `test/03_system/gui/editor_keybinding_spec.spl:142`).
- `keybinding_config_merge` (list-merge, not scalar-layer merge) deliberately
  untouched — out of scope for the scalar core, as P7 recorded.

## Adapters left in place, with deletion conditions

1. **Redundant blank/comment guard in `_kb_parse_line`** — `config_parse_line`
   already returns an empty-key entry for blank and `#` lines, so this guard is
   behaviourally dead. It is kept ONLY because
   `test/03_system/gui/editor_keybinding_spec.spl` asserts the source text
   `line.starts_with("#")` appears in `keybindings.spl`.
   **Delete when** that assertion becomes behavioural instead of source-text.
2. **`_kb_find_substr` / `_kb_extract_value`** — kept. These are substring
   search over the *within-line* `command:` / `mode:` sub-fields, which the
   scalar core does not model; they are not duplicates of `_cfg_find_char`.
   **Delete when** config_core grows a multi-field line parser (follow-up F3).
3. **`platform_config_get_by_key` uses `.to_text()` for ints, not
   `config_int_to_text`** — deliberate: `config_int_to_text` returns `""` for a
   negative input (its `while remaining > 0` loop never runs). Platform ints can
   never go negative through the validated setter, but the builtin is safe
   unconditionally. **Delete when** follow-up F2 is fixed.

## Behaviour-preservation notes (refactor, not feature change)

- **Text and bool fields resolve UNVALIDATED** (`config_resolve` +
  `config_text_to_bool`), reproducing the old `value == "true"` semantics where
  any non-`"true"` token means false. Using `config_resolve_valid` here would
  have changed behaviour (a bogus bool would fall back to the lower layer
  instead of reading as false).
- **`theme` is declared `text`, not `enum`**, in the loader schema. The old
  loader accepted any theme string; `settings_schema.spl` declares the enum for
  the UI only. Enforcing it would be a feature change (follow-up F1).
- **Int fields resolve VALIDATED** (`config_resolve_valid`), which is the
  faithful port of the `n > 0` / `n >= 0` guards. One deliberate divergence: a
  *mixed* token such as `font_size: 12x` used to be silently accepted as `12` by
  the digit-scavenging `_ec_parse_int`; it is now rejected and the lower layer
  stands. Well-formed documents are bit-identical; malformed ones now fail
  closed instead of silently mis-parsing.
- `editor_config_save` output is byte-identical (same ten keys, same order,
  same `key: value\n` shape).

## config_core follow-ups (gaps recorded, NOT forked)

- **F1 — single-source the schema.** `settings_schema.spl` still declares
  `key` / `setting_type` / `default_value` as text a second time, next to
  `editor_config_schema()` in `config.spl` (P7 duplication item 4). It was left
  alone on purpose: it also carries UI-only metadata (label, description,
  category), it declares an 11th key (`inlay_hint_refresh_delay_ms`) that is not
  an `EditorConfig` field, and its `enum` declaration for `theme` is stricter
  than the loader ever was. Collapsing the two needs a `SettingDescriptor` ⇄
  `ConfigFieldDescriptor` conversion plus a decision on enum enforcement — a
  behaviour change, so out of scope for a preservation refactor.
- **F2 — `config_int_to_text` returns `""` for negative input** (schema.spl:142,
  `while remaining > 0`). Not hit by current callers; should return `-N`.
- **F3 — no multi-field line parser.** `key: X command: Y mode: Z` needs a
  sub-field split that the scalar `key: value` core does not provide.
- **F4 — `settings_filter_by_category` / `_by_platform` in
  `settings_schema.spl` are still line-for-line twins of
  `config_filter_by_category` / `_by_platform`**, differing only in element
  type. Blocked on F1.
- **F5 — no loader-side unknown-key reporting.** `config_unknown_entry_keys`
  exists and the spec uses it, but no editor code surfaces the result yet.

## Remaining call sites (unchanged, outside this lane's exclusive paths)

All consume the unchanged public signatures and required no edits:
- `src/app/editor/editor_ctrl_core.spl:83,85,88` — get/set by key
- `src/app/editor/tui_shell_panels.spl:274` — get by key
- `src/app/editor/gui_shell_core.spl:932`, `src/app/editor/gui_shell.spl:706` — set by key
- `src/lib/editor/70.backend/gui_backend.spl:355` — get by key
- `src/lib/editor/view/settings_view.spl` — still on `SettingDescriptor` (F1/F4)
- P7 resume step 6 ("second consumer: one OS service loads through std.config")
  is NOT done — no OS service file is inside this lane's exclusive paths.

## Spec verdict

`test/01_unit/lib/editor/config_core_migration_spec.spl`

```
22 examples, 0 failures     # editor config on std.config core
6 examples, 0 failures      # platform config on std.config core
2 examples, 0 failures      # keybinding load on std.config core
```

Harness (deployed `bin/simple` is a stale seed):
`timeout 300 /tmp/cfg2/bin/cfg2job run <spec>` where `cfg2job` is a copy of
`bin/release/x86_64-unknown-linux-gnu/simple`.

Coverage: pinned `theme=light` / `font_size=18` / `tab_size=8` triple from a
representative SDN document; bool false semantics; `hover_delay_ms: 0` accepted
(min 0); unmentioned fields stay at compiled defaults; comments/blank lines
skipped (5 entries from a 7-line document); unknown key detected and ignored;
user-over-default; workspace-over-user; **mandatory-over-user**; **mandatory
survives a later session entry**; `config_is_locked` true/false; missing source
paths fall back to defaults; `font_size: 0` and `tab_size: wide` keep the lower
layer; get/set round trip incl. unknown key; SDN serialize→reparse round trip;
platform int/bool/enum set + unknown key + unrecognised platform name;
keybinding document load through the shared parser.

**Deliberate-red calibration performed.** Changing `editor_config_from_entries`
to map `tab_size: _ec_int_of(entries, "font_size")` produced
`22 examples, 4 failures` — "reads the pinned theme / font_size / tab_size
triple", "lets a workspace value override the user value", "ignores a
non-numeric tab_size and keeps the lower layer", "reloads an identical config
from its own SDN output". The mapping was restored and the spec returned to
`22 / 0`. The spec is therefore not self-comparing.

## Pre-existing specs — before / after (do-no-harm)

`before` = the three editor files restored from `HEAD` via
`git show HEAD:<path> > <path>`; `after` = this lane's versions. Same binary,
same commands, run back to back.

| Spec | Before | After | Verdict |
|---|---|---|---|
| `test/01_unit/lib/common/config_core/config_layers_spec.spl` (P7) | 31 / 0 | 31 / 0 | unchanged green |
| `test/03_system/gui/editor_settings_platform_spec.spl` | 2/0, 2/0, 2/0, 3/0 | identical | unchanged green |
| `test/03_system/gui/editor_keybinding_spec.spl` | 2/0, 25/0, 4/0, 3/0, 2/0, 2/0 | identical | unchanged green |
| `test/03_system/gui/editor_settings_gui_spec.spl` | 6/0, 3/0 | identical | unchanged green |
| `test/03_system/gui/editor_settings_schema_spec.spl` | 8/0, 6/0, **9 / 2** | identical | **PRE-EXISTING RED** |
| `test/03_system/gui/editor_keybinding_edit_spec.spl` | 2/0 ×5, **2 / 1**, 4/0, 3/0 | identical | **PRE-EXISTING RED** |
| `test/03_system/gui/editor_gui_spec.spl` | 3/0, 3/0, 2/0, **31 / 2**, 2/0, 2/0, 21/0, 10/0, **5 / 3** | identical | **PRE-EXISTING RED** |

Pre-existing failures, identical before and after, NOT caused by this lane and
NOT fixed here (out of scope):
- `editor_settings_schema_spec`: "defines editor_config_save with path
  parameter" and "declares rt_file_write_text extern" — both assert the source
  text `rt_file_write_text(path, content)` / `extern fn rt_file_write_text`,
  but `config.spl` has used `std.io_runtime.file_write` since before this lane.
- `editor_keybinding_edit_spec`: "calls rt_file_write_text to persist config" —
  same stale source-text assertion against `keybindings.spl`.
- `editor_gui_spec`: "renders and filters the quick switch picker from GUI
  controls", "renders rename preview conflicts in the LSP panel", "supports
  --gui flag for GUI mode", "registers 8 MCP tools", "has editor_mcp_dispatch
  for tool execution", "dispatches registered navigation MCP tools" — all
  unrelated to configuration.

`test/system/editor_*_spec.spl` and `test/03_system/.spipe_*` are generated
copies of the `test/03_system/gui/` specs and were not run separately.

## Blockers / not done

- P7 resume step 6 (second, non-IDE consumer of `std.config`) — blocked by this
  lane's exclusive-path list.
- Follow-ups F1–F5 above are config_core-side and belong to whoever owns
  `src/lib/common/config_core/**`.
- No commit, no push.
