# Lane P7 — std.config extraction (SimpleOS production harden)

Status: **increment 1 COMPLETE (core extracted + spec green). Uncommitted —
changes left in the working copy per lane instructions.**
Date: 2026-07-27
Plan: `doc/03_plan/agent_tasks/simpleos_production_harden_parallel.md` lane P7
Master plan: `doc/01_research/domain/simpleos_production_host_master_plan.md` §16

## Goal

Extract the *core* of the layered SDN configuration engine out of the IDE/editor
into a tier-neutral pure-function module (`src/lib/common/config_core/`), so
the IDE, System Settings, and OS services stop each re-implementing the parser,
type conversion, and per-field struct reconstruction. This increment lands the
core + spec only. The IDE call-site swap is increment 2 (see Resume plan).

## Source of extraction (READ ONLY this increment — none modified)

| File | What it contributed |
|---|---|
| `src/lib/editor/00.common/config.spl` | Layered load (`editor_config_load(user_path, workspace_path)`), SDN line parser (`_ec_apply_sdn` / `_ec_apply_line`), `_ec_parse_int`, `_ec_int_to_text`, `_ec_bool_to_text`, `_ec_digit_char`, `_ec_find_char`, per-field constraint guards, `editor_config_get_by_key` / `_set_by_key`, `editor_config_save` serializer |
| `src/lib/editor/00.common/settings_schema.spl` | `SettingDescriptor` (key/label/description/category/setting_type/default_value/enum_options/platform), `settings_filter_by_category`, `settings_filter_by_platform`, `settings_search` |
| `src/lib/editor/00.common/platform.spl` | Second copy of the `get_by_key` / `set_by_key` string ladder (`PlatformConfig`) |
| `src/lib/editor/00.common/keybindings.spl` | Third copy of the line parser (`_kb_parse_line`, `_kb_find_substr`, `_kb_extract_value`) + its own merge (`keybinding_config_merge`) and serializer (`keybinding_config_to_sdn`) |
| `src/lib/editor/view/settings_view.spl` | Consumer of the schema; re-implements category/filter helpers |

### Duplication confirmed (what §16 calls out)

1. **Parser duplicated 3×** — `config.spl:_ec_apply_sdn/_ec_apply_line`,
   `keybindings.spl:_kb_parse_line`, plus the char-scan helper duplicated as
   `_ec_find_char` / `_kb_find_substr`.
2. **Field reconstruction per field** — `_ec_apply_line` rebuilds the *entire*
   10-field `EditorConfig(...)` literal once per key (10 near-identical
   constructor calls, ~200 chars each). Adding a field means editing 10 lines.
3. **Type conversion duplicated** — `_ec_parse_int` in config.spl vs
   `extern fn parse_int` in platform.spl; bool/int→text ladders in both.
4. **Schema restates the types as text** — `settings_schema.spl` hand-declares
   `setting_type` + `default_value` as strings that must be kept in sync with
   the `EditorConfig` struct and the `_ec_apply_line` guards. Nothing enforces
   agreement. This is exactly "hand-reconstructed structs" in §16.
5. **Layering was only 2 layers, hard-coded** — `editor_config_load(user_path,
   workspace_path)` folds documents in call order. There was **no** vendor /
   machine / sysadmin / device / profile / session layer and **no mandatory
   policy ceiling** anywhere in the tree (grep for `sysadmin|mandatory` over
   `src/lib/editor`, `src/app/editor`: zero hits).

## What was extracted (new, this increment)

`src/lib/common/config_core/schema.spl` — pure, tier-neutral, no file IO:
- `ConfigFieldDescriptor` (key, label, description, category, value_type,
  default_value, enum_options, platform, min_value/max_value + has_min/has_max).
  `value_type` keeps the editor's existing vocabulary: `text|i64|bool|enum`.
  Range bounds are the faithful port of the open-coded `n > 0` (min 1) and
  `n >= 0` (min 0) guards in `_ec_apply_line`.
- Constructors `config_field`, `config_enum_field`, `config_int_field`.
- `ConfigValidation {ok, code, message}`; codes: `unknown_key`,
  `type_mismatch`, `not_in_enum`, `below_min`, `above_max`.
- `config_validate_value`, `config_validate_key_value`.
- Conversions ported verbatim: `config_parse_int` (digit-only, no sign — the
  editor never supported negatives), `config_int_to_text`, `config_bool_to_text`,
  `config_text_to_bool`, plus strict `config_is_int_text` / `config_is_bool_text`.
- Lookup: `config_schema_index` (−1 sentinel), `config_schema_has_key`,
  `config_unknown_keys`, `config_contains_text`.
- Filters ported from settings_schema: `config_filter_by_category`,
  `config_filter_by_platform`.

`src/lib/common/config_core/layers.spl` — pure, no file IO:
- `config_layer_names()` / `config_layer_rank()` — the full §16 order:
  `compiled_default(0) < vendor(1) < machine(2) < sysadmin(3) < device(4) <
  user(5) < profile(6) < workspace(7) < session(8) < mandatory(9)`.
- `ConfigEntry {key, value, layer}`, `ConfigResolution {key, value, layer,
  rank, locked}`.
- `config_parse_line` / `config_parse_layer(content, layer)` — the single
  parser, generalised from `_ec_apply_sdn`; caller supplies the text and the
  layer it came from (keeps `common/` free of IO).
- `config_entries_to_sdn` (round-trip), `config_entry_keys`.
- `config_resolve(desc, entries)` — **rank-max, not fold-in-order**. This is
  what makes mandatory policy a *ceiling*: a session/workspace entry appearing
  later in the entry list cannot displace a mandatory entry. Equal ranks resolve
  last-wins (a second `user` document overrides the first, including a second
  `mandatory` document overriding an earlier one).
- `config_resolve_valid` — same, but skips entries failing validation. This is
  the faithful port of the editor's "invalid value silently keeps the lower
  layer" behaviour from the `n > 0` guards.
- `config_resolve_all`, `config_effective_value`, `config_is_locked`,
  `config_unknown_entry_keys`, `config_invalid_entries`.

Import path convention (matches `src/lib/common/color`, `.../compress`):
`use std.common.config_core.schema.{...}` / `use std.common.config_core.layers.{...}`.

## What was deliberately LEFT OUT (not in this increment)

- **File IO / load order** — `common/` is tier-neutral; `file_read`/`file_write`
  stay at the caller (nogc_sync_mut). Increment 2 supplies a thin loader.
- **Transactions** (validate-all → prepare → apply → verify → commit/rollback),
  **watch**, **secrets**, **migrate/repair**, **`simple config doctor`**,
  **VS Code importer/exporter**, **ui_model** — all §16 items, later increments.
- **Nested/structured SDN** — the extracted parser handles the flat `key: value`
  document the editor actually uses. Structured SDN goes through `std.sdn` when
  a caller needs it.
- **Keybinding merge semantics** (`keybinding_config_merge`) — list-merge, not
  scalar-layer merge; a separate extraction.
- **No IDE file was modified.** `src/lib/editor/**` is untouched.

## Spec verdict

`test/01_unit/lib/common/config_core/config_layers_spec.spl`

```
31 examples, 0 failures
```

Harness (per lane recipe; deployed `bin/simple` is a stale seed):
`timeout 300 /tmp/p7lane/bin/p7job run test/01_unit/lib/common/config_core/config_layers_spec.spl`
where `p7job` = copy of `bin/release/x86_64-unknown-linux-gnu/simple`.

**Deliberate-red calibration performed.** Changing `config_resolve`'s rank-max
guard (`if rank >= best_rank`) to plain fold-in-order (`if rank >= 0`) produced
`31 examples, 3 failures` — exactly the three ceiling/precedence assertions
("ignores a lower layer even when it appears later", "overrides a user value
even though the user entry comes later", "overrides the session layer"). The
guard was restored and the spec returned to `31 examples, 0 failures`. The spec
therefore genuinely tests the ceiling and is not self-comparing.

Coverage: layer rank table + unknown layer; default fallback; user-over-default;
workspace-over-user; lower-layer-later-in-list ignored; same-layer last-wins;
mandatory over user; mandatory over session; `config_is_locked`; mandatory
replaced by newer mandatory; accept/reject i64; accept/reject bool; below_min;
zero accepted when min is 0; not_in_enum; invalid higher layer keeps lower
layer; unknown key in list / in key-value pair / in parsed entries; schema
has_key; invalid-entry collection; document parse with comments and blanks;
final line without newline; SDN round-trip; two-document effective resolution;
resolve_all; int/bool conversion.

## Defects found while doing this work (both PRE-EXISTING, not caused by P7)

### D1 — parser folds a bare trailing `-1` into the previous line (WRONG RESULT, silent)

A function ending in the sentinel form

```
    if layer == "mandatory": return 9
    -1
```

evaluates `config_layer_rank("mandatory")` to **8**, and returns **nil** for the
fallthrough case. The `-1` on its own line is being parsed as a binary minus
continuing the previous inline-`if` body (`9` then `-1` → `9 - 1`).

Minimal repro (`/tmp/p7lane/repro.spl`, reproduced on the lane binary):
inline `if cond: return <int literal>` immediately followed by a bare `-1` at
function-body indent. Trigger requires the *inline* if-form; the block form
(`if cond:` newline `return 9`) parses correctly. `return -1` and `0 - 1` are
both unaffected. The nil fallthrough then crashes `print` (core dump).

This is dangerous because the same sentinel idiom (`-1` as last expression) is
used throughout the repo — it is only safe there because it follows a `while`
block rather than an inline `if`. Severity: silent wrong value, no diagnostic.

Workaround applied in `layers.spl:config_layer_rank` — explicit `return -1`,
with an inline comment pointing at this file. **The grammar bug itself is NOT
fixed** (compiler source is outside lane P7's exclusive paths). Needs filing
against the parser by whoever owns `src/compiler/`.

### D2 — lint COLL006 "string concat in loop" false-positives on integer counters

`bin/simple lint` reports `error[COLL006]: string concat in loop (O(n^2))` for
functions that contain **no string concatenation at all**. Minimal repro:

```
fn count_digits(s: text) -> i64:
    var n = 0
    var i = 0
    while i < s.len():
        n = n + 1
        i = i + 1
    n
```

→ `2 error(s)`. Conversely the rule *misses* `config_int_to_text`, which is a
genuine string-concat loop. It appears to fire on any `while` body containing
`x = x + <expr>`, regardless of type, and reports the function's first line as
the location.

Pre-existing: the same rule fires on the untouched extraction sources
(`src/lib/editor/00.common/config.spl` + `settings_schema.spl` → 3 errors).
Lane P7 did not introduce it and did not distort code to appease it. Needs
filing against the linter rule.

The other lint finding (`unnamed_duplicate_typed_args`) WAS fixed in P7 code —
all duplicate-typed positional calls are now named. Remaining lint failures on
`config_core/*` are D2 false positives only.

## Resume plan — increment 2 (IDE call-site swap)

Preconditions: this increment's files committed; no other lane owns
`src/lib/editor/**` (verify before starting — the parallel plan does not
currently assign it, but P7's row in the plan table names "IDE call-site swap"
as P7-owned).

1. **Add the editor schema in the new vocabulary.** New function in
   `src/lib/editor/00.common/settings_schema.spl` returning
   `[ConfigFieldDescriptor]` built with `config_field` / `config_enum_field` /
   `config_int_field`, carrying the same 11 editor keys + 7 keybinding keys + 6
   platform keys currently declared as `SettingDescriptor`. Keep
   `SettingDescriptor` as a thin alias-shaped adapter until `settings_view.spl`
   is converted, then delete it (deletion condition: no remaining reference to
   `SettingDescriptor`).
2. **Rewrite `editor_config_load`** as:
   `file_read` each layer path → `config_parse_layer(text, layer)` → concat
   entries → `config_resolve_valid` per field → build `EditorConfig` once.
   This deletes `_ec_apply_sdn`, `_ec_apply_line` (the 10 duplicated
   constructor literals), `_ec_find_char`, `_ec_parse_int`, `_ec_int_to_text`,
   `_ec_bool_to_text`, `_ec_digit_char` — roughly 100 of config.spl's 179 lines.
3. **Widen the load signature** from `(user_path, workspace_path)` to a list of
   `(path, layer)` pairs so vendor/machine/sysadmin/device/profile/session/
   mandatory become reachable. Mandatory policy path must be read last **and**
   is enforced by rank, not by ordering.
4. **Convert `platform.spl`** `platform_config_get_by_key`/`_set_by_key` to
   `config_effective_value` + descriptors; drop `extern fn parse_int`.
5. **Convert `keybindings.spl`** `_kb_parse_line` to `config_parse_line`
   (keep the list-merge semantics, which are out of scope for the scalar core).
6. **Second consumer** (lane gate requires "IDE + one service load through
   std.config"): pick the smallest OS service with an SDN config and route it
   through `config_core`, proving the module is genuinely tier-neutral.
7. **Round-trip spec** at `test/01_unit/lib/editor/` (or the lane's test dir):
   load a multi-layer fixture → mutate → serialize → reload → identical, plus
   a mandatory-policy-pins-a-key case at the IDE level.
8. Re-run this spec plus the editor config specs; both must stay green.

Do NOT rename `config_core` to `config` while `src/lib/editor/00.common/config.spl`
still exists — a `std.common.config` module next to an editor `config.spl` is
exactly the name-collision class recorded in memory (interp flat registry
hijacks explicit `use` imports). Rename only after step 2 lands and the editor
file is reduced to a facade.

## Files changed by this lane (uncommitted)

- `src/lib/common/config_core/schema.spl` (new)
- `src/lib/common/config_core/layers.spl` (new)
- `test/01_unit/lib/common/config_core/config_layers_spec.spl` (new)
- `.spipe/simpleos_harden_p7_config/state.md` (this file)

Nothing else touched. No commit, no push.
