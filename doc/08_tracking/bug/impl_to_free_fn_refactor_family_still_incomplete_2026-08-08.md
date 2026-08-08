# impl-to-free-fn refactor damage: family declared closed but ~60 zero-definition sites survive

- **Filed:** 2026-08-08
- **Severity:** High (dead call sites in live compiler passes; silent no-ops / unresolved calls)
- **Status:** OPEN
- **Found by:** adversarial review of `b0c98541d2a`, `bc052a4470d`

## Summary

`b0c98541d2a` ("restore folded-receiver method calls, shape (d) refactor
damage", 8 files) and `bc052a4470d` ("restore cycle_detector.spl free-function
calls", 1 file) both present themselves as closing the impl-to-free-fn
refactor-damage family. They do not. A fail-closed tree-wide sweep finds ~60
surviving call sites of the same two damage shapes whose callee has **zero
`fn`/`me` definitions anywhere in `src/`**.

Six of the survivors are in files those two commits *edited* — the sweeps were
per-line, not per-file.

## Damage shapes

1. `recv.<X>_<Y>(<X>, ...)` — folded receiver, first argument re-passed.
2. `<X>_<Y>(<X>, ...)` — bare free-function form (the `bc052a4470d` cluster).

## Oracle (fail-closed, reproducible)

```sh
# all fn/me definition names tree-wide (deliberately over-broad => fail-closed)
/usr/bin/grep -rEoh '\b(fn|me)[[:space:]]+[a-zA-Z0-9_]+' src/ --include=*.spl \
  | /usr/bin/sed -E 's/.*[[:space:]]//' | sort -u > defs.txt

# shape 1
/usr/bin/grep -rEn '[a-z0-9_]+\.([a-z0-9_]+)_[a-z0-9_]+\(\1[,)]' src/ --include=*.spl
# shape 2
/usr/bin/grep -rEn '(^|[^.a-zA-Z0-9_])([a-z0-9_]+)_[a-z0-9_]+\(\2[,)]' src/ --include=*.spl
```
For each hit, extract the callee name and reject it if it appears in `defs.txt`.
A callee with **zero** definitions is a surviving damage site. Use `/usr/bin/grep`
(ugrep is the default `grep` here) and `-r` (not `-R`) so the `mir`/`hir`/
`driver`/`backend` symlinks are not followed into double counts.

## Surviving sites

### In files the two reviewed commits edited (missed line-by-line)

**The "candidate restore" column is UNVERIFIED and must be confirmed per row
before use.** The oracle proves only that the *called* name has zero
definitions; it says nothing about what the correct target is. This repo's
free-function convention is `<lowercased-type>_<method>(self, ...)`, so the
right restore is often a *differently-prefixed free function*, not a dotted
call — e.g. `hygiene.spl:337`'s `ident_add_mark(ident, ...)` restores to
`markedident_add_mark(ident, ...)` (defined at `hygiene.spl:64`), NOT to
`ident.add_mark(...)`. Likewise `HygieneScope`'s helpers are named
`hygienescope_*` (`hygiene.spl:116,127`), so `scope_bind`/`scope_lookup`
probably restore to `hygienescope_bind`/`hygienescope_lookup` — confirm the
target exists before editing.

| file:line | dead call (zero definitions tree-wide) | candidate restore (UNVERIFIED) |
|---|---|---|
| `src/compiler/35.semantics/macro_check/hygiene.spl:222` | `scope_bind(scope, name, ident)` | `hygienescope_bind(scope, name, ident)`? |
| `src/compiler/35.semantics/macro_check/hygiene.spl:239` | `scope_lookup(scope, ident.name)` | `hygienescope_lookup(scope, ident.name)`? |
| `src/compiler/35.semantics/macro_check/hygiene.spl:290` | `scope_lookup(scope, name)` | `hygienescope_lookup(scope, name)`? |
| `src/compiler/35.semantics/macro_check/hygiene.spl:337` | `ident_add_mark(ident, self.current_mark)` | `markedident_add_mark(ident, self.current_mark)` (target CONFIRMED at `hygiene.spl:64`) |
| `src/compiler/35.semantics/macro_check/template.spl:165` | `kind_can_follow(kind, prev_kind)` | ? |
| `src/compiler/35.semantics/macro_check/template.spl:277` | `param.kind_to_text(kind)` | ? |
| `src/compiler/35.semantics/macro_check/template.spl:300` | `kind_to_text(kind)` | ? |
| `src/compiler/35.semantics/macro_check/mod.spl:207` | `args_len(args)` — sole tree-wide definition is `src/app/ui.tauri/tauri_entry.spl:15` (`[text] -> i64`), an unrelated app module. Under the flat bare-name function table this can resolve to the WRONG function rather than fail (see `9918298a7240`). | ? |
| `src/compiler/70.backend/backend/exhaustiveness_validator.spl:117` | `pattern_get_severity(pattern)` | ? |
| `src/compiler/70.backend/backend/exhaustiveness_validator.spl:405` | `pattern_is_error(pattern)` | ? |
| `src/compiler/70.backend/backend/exhaustiveness_validator.spl:474` | `std.sys_exit(sys, 1)` | ? |

`macro_check/mod.spl:206`'s `validator.params.keys().len()` — the one place
`b0c98541d2a` deliberately changed semantics — is **CORRECT**: `params` is
`Dict<text, TemplateParam>` (`template.spl:124`), so `Dict.len()` would have
returned -1 under native codegen.

### Elsewhere (never swept)

`src/compiler/55.borrow/gc_analysis/mod.spl:119,120,124` — `gc_types_contains`
/ `gc_types_push` (**fixed in the commit that adds this doc**).

**Same file, DIFFERENT damage shape, still open:**
`src/compiler/55.borrow/gc_analysis/mod.spl:129` and `:132` pass a bare `_1`
placeholder — `RootAnalysis.create(self.is_gc_type(_1))`. `_1` is not bound in
either scope; this looks like a lambda/closure argument mangled by the same
refactor (`\x -> self.is_gc_type(x)` collapsed to a positional placeholder that
the language does not support here). Not covered by either regex shape above,
so a sweep that only chases `<X>_<Y>(<X>)` will not surface it. Deliberately
left unfixed here because the intended closure form is a guess.

Still open:

- `src/compiler/30.types/type_system/effects.spl:117` `callee_effect_value_is_async(callee_effect_value)`; `:228` `scc_contains(scc, callee)`; `:309` `effect_is_sync(effect)`; `:353` `effect_value_is_async(effect_value)`; `:361` `effect_value_is_sync(effect_value)`
- `src/compiler/00.common/dependency/resolution.spl:95` `mp_segments(mp)`; `:97` `segs_len(segs)`; `:129,130,157` `fs_has_file(fs, ...)`
- `src/compiler/35.semantics/visibility_checker.spl:111` `checker_check_symbol_access(checker, ...)`; `:270` `symbol_table_lookup(symbol_table, name)`; `:272` `symbol_table_get(symbol_table, sym_value)`
- `src/compiler/15.blocks/blocks/validators.spl:100` `key_len(key)`; `:109` `elements_len(elements)`; `:143` `query.raw_lower(raw)`
- `src/compiler/15.blocks/blocks/testing.spl:84` `error.message_contains(message, expected_message)`; `:294` `value_type_name(value)`
- `src/compiler/15.blocks/blocks/registry.spl:26,182` `blk_lexer_mode(blk)`
- `src/compiler/15.blocks/blocks/definition.spl:60` `parser_set_mode(parser, ...)`; `:61` `parser_parse_expr(parser)`
- `src/compiler/15.blocks/blocks/easy.spl:113` `pattern_trim(pattern)`
- `src/compiler/15.blocks/blocks/text_transforms.spl:37` `vars_items(vars)`
- `src/compiler/00.common/predicate_parser.spl:125` `tokens_len(tokens)`
- `src/compiler/70.backend/backend/common/type_mapper.spl:23` `mapper_map_type(mapper, mir_type)`
- `src/compiler/70.backend/backend/vulkan_backend.spl:100` `backend_compile(backend, mir_module)`
- `src/compiler/35.semantics/semantics/binary_ops.spl:120` `result_wrapping_mul(result, base)`; `:123` `base_wrapping_mul(base, base)`
- `src/compiler/35.semantics/macro_contracts.spl:104` `existing_symbols_contains(existing_symbols, item.name)`
- `src/compiler/40.mono/monomorphize/util.spl:112` `elems_first(elems)`
- `src/compiler/10.frontend/desugar/desugar_async.spl:44` `response_text(response)`; `:227` `future_expr_poll(future_expr, waker)` — and the duplicate copy at `src/compiler/90.tools/desugar_async.spl:42,225`, plus `:122` `analysis.suspension_points_len(suspension_points)`
- `src/compiler/99.loader/loader/smf_mmap_native.spl:106` `result_reserve(result, length)`
- `src/lib/nogc_sync_mut/fuzz.spl:164,169,199,231,246,291,299` `rng_next_range(rng, ...)`
- `src/app/cli/commands/test_batch.spl:69` `dir_list_recursive(dir)`
- `src/os/kernel/fs/win_vfs/win_vfs_driver.spl:145` `tree_readdir(tree, path)`; `:157` `tree_read(tree, path)`
- `src/compiler_rust/lib/std/src/tooling/dashboard/snapshots.spl:147` `date_diff_days(date, today)`
- `src/compiler_rust/lib/std/src/spec/formatter/markdown.spl:164` `path_file_exists(path)`

Known false positives of the regex (do NOT "fix" these): `me fn
cluster_to_sector` in `fat32_core.spl` (real method, the oracle's def regex must
allow `me fn`); `queue_send`/`queue_recv`/`queue_poll`/`queue_close` in
`src/os/kernel/ipc/syscall_spm.spl` (docstring text, not code); `lut_lookup` in
`backend_metal_msl.spl` (embedded MSL shader source); `is_lowercase`, `to_u64`
(builtins).

## Failure scenario

`hygiene.spl:239`'s `scope_lookup(scope, ident.name)` resolves to nothing.
Macro-hygiene identifier resolution therefore never finds an existing binding, so
`check_hygiene` on a macro expansion that shadows an outer name reports no
conflict where it should — a silently-skipped semantic check, not a crash.
Unresolved calls are only WARNINGS in pure-Simple, so a clean build is not
evidence against this.

## Why the sweeps missed them

Both commits sized the family from a hand-maintained tracking doc
(`impl_to_free_fn_refactor_family_sweep_2026-08-07.md`, "23 sites / 8 files")
plus a `self.`-scoped grep. Neither ran a definition-existence oracle over the
whole tree, so anything on a non-`self.` receiver or in an unlisted file was
invisible. `b0c98541d2a`'s own message notes the doc "undercounted" — that
observation was applied to four extra lines, not turned into a systematic sweep.

## Fix plan

Run the oracle above, restore each site, and re-run the oracle to zero before
declaring the family closed. Do NOT size the family from `unresolved call` build
warnings — that diagnostic samples rather than enumerates.

## Related

- `b0c98541d2a`, `bc052a4470d` (the two incomplete restorations)
- `doc/08_tracking/bug/impl_to_free_fn_refactor_family_sweep_2026-08-07.md`
- `.claude/rules/code-style.md` (native-codegen Dict pitfalls, applied by both commits)
