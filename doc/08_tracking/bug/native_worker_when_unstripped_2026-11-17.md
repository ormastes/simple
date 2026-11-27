# Native phase-3 worker parse sees unstripped top-level `@when(...):`

Status: verification-pending (root cause located 2026-11-17; fix in work/file-worker-when-fix-20261117 — needs a phase-3 workers-on native run)

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
1. **Closed (2026-11-18):** Native-only text compares in `parser_preprocessor.spl` that used
   `text[i]` (`_pp_tokenize_condition`, `_pp_extract_paren_condition`, `_pp_target_indent`,
   `_pp_leading_ws`, and the `@cfg` skip indent/brace scans): `text[i]` yields `char`
   (ADR-005). Replaced every `text[i]` indexing site with byte-bounded `.byte_len()` +
   `.substring(i, i + 1)` comparisons against single-char `"..."` text literals (and shared
   `_pp_target_indent` / `_pp_line_brace_delta` helpers) so interpreter and compiled native
   LLVM/Cranelift engines agree.
2. A parse in the worker child that bypasses `_pp_preprocess_conditionals` (child-process
   route, not the parent's): reproduce with the full phase-3 env and
   `SIMPLE_COMPILER_TRACE=1 SIMPLE_FRONTEND_CACHE_BOUNDARY_PROFILE=1` and a cold
   frontend cache, then flip one knob per run (`--target`, `--entry-closure`, workers off,
   `SIMPLE_WORKER_ADMITTED_MEMO=0`). A minimal `native-build` of a 7-line `@when` file did
   not finish within 400 s on this host (whole std closure), so this needs the phase-3 lane.

## Root cause (2026-11-17)
A worker builds an empty PLACEHOLDER surface for every module outside its closure slice
(`worker_mode == 2`, `driver_source_parse_selected.spl` `add_streaming_module_surface`).
The placeholder parse text was `""`, parsed under the module's REAL path. Preprocessing
ran on `""` (a no-op), then `lex_init_with_path` (`10.frontend/core/lexer.spl`) saw an
empty source with a named path and re-read the file from disk -- the defense against the
old "reads every source as empty" native bug. The lexer therefore lexed the RAW file, with
every `@when(...):` / `@else:` intact. Directive-free files parsed "fine" (raw = selected),
which is why only the files with top-level directives failed. `SIMPLE_FILE_WORKERS=0`
builds no placeholders. The earlier "workers off is clean" bisect was also cache-masked:
the p5nw run reported every phase-2 parse as `cached`.

Side effects of the old behaviour: placeholder surfaces were never empty (they carried the
raw file's declarations), and every placeholder shared one private parse-cache key
(`xxh3("")`), so a stored raw parse could be restored for another module's placeholder.

Evidence: interpreter control (`seed_p1 test`) parsing `""` under a fixture path with a
top-level `@when(os="windows"):` prints `[parser_error] line 2:20: unexpected token in
expression: : ':'` -- the exact native symptom. The worker unit child log
(`native-build-stderr-30880-2.log`) shows the same errors after `[file-worker] unit picked=1`.

## Fix
`driver_worker_placeholder_parse_text_v1()` (`driver_hir_worker_surface_v1.spl`) returns a
non-empty empty module (`"\n"`); mode 2 parses it, so the lexer never touches the disk.
Spec: `test/01_unit/compiler/80.driver/hir_worker_placeholder_parse_text_spec.spl`
(red before: helper missing / `""` control reproduces 2:20; green after).

Additional fix (2026-11-18, `src/compiler/10.frontend/core/parser_preprocessor.spl`):
- Replaced all remaining `text[i]` character indexing sites in `_pp_tokenize_condition`,
  `_pp_extract_paren_condition`, `_pp_target_indent`, `_pp_leading_ws`, and the second-pass
  `@cfg` skip indentation / `{}` brace-counting loops (consolidated into `_pp_target_indent`
  and `_pp_line_brace_delta`) with `.byte_len()` + `.substring(i, i + 1)` comparisons so
  native LLVM/Cranelift and interpreter builds share identical text-comparison semantics.
- Regression spec: `test/01_unit/compiler/10.frontend/parser_preprocessor_byte_slice_spec.spl`
  (7/7 examples passing under `simple.exe test --mode=interpreter`), plus
  `test/01_unit/compiler/80.driver/hir_worker_placeholder_parse_text_spec.spl` (2/2) and
  existing preprocessor specs.
- Verified zero `nil` outside `unsafe:` via
  `sh scripts/check/check-nil-outside-unsafe-added.shs --rank`.
- Native compilation / phase-3 workers-on cold-cache gate remains `verification-pending`
  (not run in this interpreter-only lane).

Behaviour change to watch: placeholder surfaces are now truly empty. If
`worker_admitted_closure_v1` misses a module a worker needs, phase 3 may now surface
unresolved-import errors that the raw re-read used to hide.

Not verified: that the in-process coordinator stream (`native-build-stderr-30880-1.log`,
no `[parser_error]` lines, no closure-phase marker) goes through the same mode-2 route.
Gate: phase-3 `native-build` with file workers on and a cold frontend cache.

Lexer hazard left in place (separate bug): `lexer_empty_source_disk_reread_bypasses_preprocess_2026-11-17.md`.
