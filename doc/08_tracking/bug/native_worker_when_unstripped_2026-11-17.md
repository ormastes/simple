# Native phase-3 worker parse sees unstripped top-level `@when(...):`

Status: open (root cause NOT yet located; investigation notes only — no fix landed)

## Symptom
stage2d (release/1.0.0 tip + PR #9884) phase-3 `native-build --target x86_64-pc-windows-gnu
--entry-closure` with file workers, `SIMPLE_UNIT_TLDR_IMPORTS=0 SIMPLE_WORKER_ADMITTED_MEMO=1
SIMPLE_UNIT_ORDER_INDEX=1`:

    [streaming-parse-failure] .../io/path_identity_abi.spl: parse error ...: 2:20:unexpected token in expression: : ':'

Same for path_identity.spl:23, windows_image_owner.spl:34, windows_redirected_process.spl:8,
linux_helper_root_v1.spl:9, sffi/process_memory.spl:64, common/io/read_only_file_view.spl:239.
Every reported position is exactly a `@when(...)` directive line, so the parser lexed text
in which the directive was not blanked.

## Ruled out (2026-11-17)
- Source producers: `module_surface_skeleton_v1` keeps directive lines verbatim and on the
  same line; `path_identity_abi.spl` has no bodies so its skeleton == source.
  `driver_surface_parse_text_v1` / `worker_surface_text_v1` only return source or skeleton.
- Frontend entries reached from `add_streaming_module_surface`
  (`driver_source_parse_selected.spl:276`) all preprocess before parsing:
  `parse_full_frontend_with_scope` (frontend.spl:231) and
  `parse_full_frontend_target_receipted_scope_v1` (frontend.spl:335).
  The target-receipted route rejects a skeleton by digest ("digest differs"), not a parse error.
- Native preprocessor itself: same stage2d binary, `compile --format=smf` of
  `path_identity.spl` parses clean with and without `--target x86_64-pc-windows-gnu`,
  with and without `SIMPLE_HIR_CFG_SELECT=1`, and with
  `SIMPLE_HIR_SHARD=0/1 SIMPLE_HIR_WORKER_SKELETON=1` (that run was a frontend-cache hit:
  `hits=11 parses=0`, so the user-level parse cache can mask the failing route).
- PR #9884 touches only `_ParserDecls/enum_module_body.spl` (`pub unit`), not the preprocessor.

## Open suspects (next steps)
1. Native-only text compares in `parser_preprocessor.spl` that use `line[i] == "("`
   (`_pp_extract_paren_condition`, `_pp_target_indent`, `_pp_leading_ws`): `text[i]`
   yields `char` (ADR-005). These do not by themselves leave the directive line, but make
   conditions evaluate wrongly natively.
2. A parse in the worker child that bypasses `_pp_preprocess_conditionals` (child-process
   route, not the parent's): reproduce with the full phase-3 env and
   `SIMPLE_COMPILER_TRACE=1 SIMPLE_FRONTEND_CACHE_BOUNDARY_PROFILE=1` and a cold
   frontend cache, then flip one knob per run (`--target`, `--entry-closure`, workers off,
   `SIMPLE_WORKER_ADMITTED_MEMO=0`). A minimal `native-build` of a 7-line `@when` file did
   not finish within 400 s on this host (whole std closure), so this needs the phase-3 lane.
