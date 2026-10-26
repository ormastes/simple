# `dict[k] ?? d` on Dict<text, text> yields raw 0 on a miss (2026-10-25)

**Status:** open

## Symptom
Phase 3 Stage 3 (`simple.r7`, `simple.pu3`), in-process native-build route
(`native-build src/app/zz_r27_t/h.spl ...`, positional, no `--entry`/`--source`,
which bootstrap_main routes straight into CompilerDriver):

    error: in-process native-build: compiler entry '' collected zero source files

## Root cause (gdb + objdump of the run-27e object)
`driver_explicit_source_entry` = `ctx.config["compiler_source_entry"] ?? ""`
compiles to:

    rt_dict_get(config, key) -> rt_interp_cstr(v) -> rt_is_some(cstr) -> rt_unwrap_or_self

The Dict<_, text> index result is decoded to text (rt_interp_cstr) BEFORE the
`??` nil test. On a missing key rt_dict_get returns RT_NIL (3);
`rt_interp_cstr(3)` returns NULL; `rt_is_some(0)` is true; the function returns
raw 0. Callers then see `0 != ""` as true, take a phantom explicit entry, and
load zero sources. gdb: `finish` from driver_explicit_source_entry -> x0 = 0x0.

26 lines match `config\[[^]]*\] ??` under src/compiler (all in 80.driver; 44 including src/app) (e.g.
`(ctx.config["mcdc_mode"] ?? "off") == "off"` is false on a miss).

## Workaround (this change)
`driver_config_text_or(ctx, key, default)` in driver_phase_gates.spl tests
`contains_key` first; driver_explicit_source_entry and both mcdc_mode reads use
it. Tagged `@workaround`. Interim object for the Stage 3 link: a C forward of
`driver_explicit_source_entry` plus the run-27e object with that symbol
weakened (see S/r27/bp/objs/).

## Compiler fix (open)
MIR NullCoalesce must test the raw rt_dict_get result for nil before any text
decode of the Dict value (expr_dispatch.spl NullCoalesce arm; the Index
lowering decodes eagerly). Not fixed here; takes effect only once Phase 3
rebuilds itself.
