# Stage 2 parse shard SIGSEGV in `named_type_find` (companion public-summary re-parse)

- id: stage2_parse_shard_segv_named_type_find_2026-11-13
- status: open
- severity: P2 (parse warm-up shards die; the build continues without the
  parser cache, so every downstream phase pays a cold parse)
- found: 2026-11-13, bootstrap-fable-17 Phase 2 matrix `test_runner_build`
- binary: run 17 Stage 2, `.../pinned-ea253974c0e4/build/bootstrap-fable-17/stage3/aarch64-unknown-linux-gnu/stage2-admitted/simple`
  (sha256 `a345c68a253f61778ae4ae8b24cf7eb5abbfd4af1e26870d30d112a95207c616`), aarch64 Linux

## Symptom

Both parse shards of the coordinator die with signal 11, are retried once,
and die again:

```
[parse-shard] shard=0/2 pid=981938 FAILED exit=-139
[parse-shard] shard=1/2 pid=981939 FAILED exit=-139
...
[parse-shard] 0/2 shard(s) completed split=queue
```

## Why it shows up now

Before run 17 the parse and HIR pools never ran on the Phase C tool rows:
under the pre-`fb5a084c30f` seed, `match raw.to_i64(): case Some(value)` in
`native_build_closure_selected_count_v1` (src/app/cli/native_build_main.spl)
bound 3 instead of the published closure size, so the small-closure clamp
(`native_build_shard_count_for_closure_v1`, max 4) zeroed every shard phase
(measured: run 13 and run 16 Stage 2 binaries log `closure_files=3`, run 17's
logs `closure_files=3134`). The crash is latent, not a regression of run 17.

## Reproduction (T0, ~40 s)

From a checkout (`/home/yoon/dev/simple-rowenv-20261112` used), with the run 17
Stage 2 binary and the Phase C row environment (`SIMPLE_FILE_WORKERS=0`,
`SIMPLE_MIR_SHARD_COUNT=8`, managed tool/runtime authority, `SIMPLE_SHARD_MEM_CLAMP=1`,
`SIMPLE_BOOTSTRAP_RSS_CAP_MODE=enforce`, etc.), run

```
<stage2> native-build <entry> --backend=cranelift --low-memory --entry-closure \
  --cache-dir <scratch>/cache/full-cli --timeout 60 --threads 2 -o <scratch>/out
```

| entry | closure | parse shards |
|---|---|---|
| `src/app/test_runner_new/main.spl` | 333 | 4/4 SIGSEGV (2 shards x 2 attempts) |
| `src/compiler/bootstrap_admission/stage2_result_map_storage_roots.spl` (`SIMPLE_SHARD_SMALL_CLOSURE_MAX=0`) | 11 | 3/4 SIGSEGV (non-deterministic) |
| `src/compiler/bootstrap_admission/stage2_nominal_owner_keys.spl` (`SIMPLE_SHARD_SMALL_CLOSURE_MAX=0`) | 562 | 4/4 SIGSEGV |
| `hello_world.spl`, `p2_add.spl` (1-file closures) | 1 | exit 0 |

A captured child (`/proc/<pid>/cmdline` + `environ`) replays the crash
standalone: `<stage2> run src/app/cli/parse_shard_main.spl <row args>
--internal-environment-variant-policy-v1=<handoff> --parse-fibers=0/2`.

## Backtrace (gdb, replayed child)

```
#0  __strlen_asimd ()                         x0 = 0x8100000000000000
#1  simple_runtime::value::collections::rt_text_eq_any::bytes_of ()
#2  rt_text_eq_any ()
#3  compiler.frontend.core.types.named_type_find ()
#4  compiler.frontend.core.parser.parser_parse_type_impl ()
#5  compiler.frontend.core.parser.parser_parse_type ()
#6  ..._ParserDecls__fn_struct_decls__parse_extern_fn_decl ()
#7  ..._ParserDecls__enum_module_body__parse_module_decl_with_visibility ()
#8  ..._ParserDecls__enum_module_body__parse_module_body ()
#9  compiler__frontend__core__parser___parse_module_with_diagnostics ()
#10 compiler.frontend.core.parser.parse_module_silent_checked ()
#11 compiler.frontend.cache_artifact.public_summary_projector.project_public_summary_v1 ()
#12 compiler.driver.cache.module_artifacts_v1.module_tldr_companion_view_sections_with_macros_v1 ()
#13 compiler.driver.cache.module_artifacts_v1.module_tldr_companion_view_sections_v1 ()
#14 compiler__driver__driver_parse_shard_entry___driver_run_parse_fibers ()
#15 compiler.driver.driver_parse_shard_entry.driver_run_parse_fibers_with_environment_variant_policy_v1 ()
#16 app.cli.parse_shard_main.run_parse_shard ()
```

`named_type_find` (src/compiler/10.frontend/core/types.spl:863) compares
`named_type_names[i] == name`; one element is not a live text handle
(`0x8100000000000000` handed to `strlen`).

## Analysis (not yet root-caused)

The crash is in the second, low-level parse that the parse-fiber loop runs per
file (`driver_parse_shard_entry.spl` `_driver_run_parse_fibers`:
`parse_full_frontend_selected_v1` then `module_tldr_companion_view_sections_v1`
-> `project_public_summary_v1` -> `parse_module_silent_checked`). `types.spl`
`type_pools_promote_hir_owners` (called from `parser_promote_transient_owners`)
documents exactly this hazard ("Public-summary validation performs a low-level
parse after the retained full parse's scratch scope ends ... their live owners
must survive too") and promotes `named_type_names`, so the promotion is wired;
an element of the registry nevertheless reaches the re-parse dead. Leading
hypothesis: an element registered in a later file's transient scope (pool reset
per file, FileFiber window of several files) is reclaimed before that file's
companion re-parse, or the promote copies the array but not a text element
allocated in the transient heap. Non-determinism on the 11-file closure points
at allocation/reclaim order rather than parser logic. Single-file closures do
not crash.

## Next steps

1. Run the 11-file repro with `SIMPLE_POOLDBG=1` (flat_pool_debug_state_v1) to
   see which file and pool generation the dead element belongs to.
2. Check whether `rt_transient_heap_promote` on `[named_type_names]` promotes
   the text elements or only the array spine.
3. Pin with a seed/native spec that parses two modules through the fiber
   window and then re-parses the first through `project_public_summary_v1`.
