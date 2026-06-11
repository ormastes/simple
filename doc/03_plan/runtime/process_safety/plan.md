# Plan: Process Kill Safety — Crash Fix Rollout

Status: guards landed on main (commit `4029a43d4ba8`, 2026-06-10).
Background: `doc/07_guide/runtime/process_kill_safety.md` (session-killing
`kill(-1)` broadcasts on 2026-06-08 ×3 and 2026-06-10).

## Done

- [x] Diagnose crash signature (journal: exit.target + simultaneous SSH/tmux
      teardown; OOM/network/logind ruled out).
- [x] Audit all kill paths in repo (C runtime, Rust runtime, `.spl` libs,
      `.shs` scripts, test runner, kill monitor).
- [x] Guard `rt_fork_parent_wait` (`src/runtime/runtime_fork.c`) — `child_pid <= 0 → -1`.
- [x] Guard `native_process_kill` (`runtime/src/value/file_io/process.rs`).
- [x] Guard `native_process_terminate` (`runtime/src/value/process.rs`).
- [x] Verify: `gcc -fsyntax-only` + `cargo check -p simple-runtime` clean.
- [x] Guide + TLDR under `doc/07_guide/runtime/`; spipe skill exception note.

## Remaining

- [x] Rebuild Rust seed (`cd src/compiler_rust && cargo build --profile bootstrap -p simple-driver -p simple-native-all`)
      so interpreter-mode `bin/simple` carries the Rust-side guards.
      (Done 2026-06-10 07:38; seed deployed to `bin/release/x86_64-unknown-linux-gnu/simple` 09:18.)
- [x] `scripts/bootstrap/bootstrap-from-scratch.sh --deploy` — ran 2026-06-10
      (script restored from git history after deletion in `4cf561567f`; helper
      paths repointed to `scripts/setup/*.shs`). Stage 2 OK, stage 3 known-fail
      (LIM-010), but the stage-4 cranelift full-CLI binary it deployed
      **re-execs itself in a loop** when given a `.spl` file (fork bomb;
      see BUG below). Reverted the deploy to the freshly built Rust seed,
      which carries the Rust-side guards. The C-runtime guard
      (`rt_fork_parent_wait`) is not linked into `bin/simple` at all — it is
      compiled fresh from `src/runtime/runtime_fork.c` by
      `compile_runtime_objects` whenever a native binary is linked, so every
      future native build picks up the guard from source automatically.
- [x] BUG (fixed 2026-06-10): stage-4 full-CLI binary exec-looped on
      `simple <file.spl>` / `simple run` / `-c`. Root cause:
      `_cli_driver_binary()` returns `bin/simple` and
      `cli_run_file`/`cli_run_code`/`run_native_build_bootstrap` spawn it —
      when the compiled CLI IS `bin/simple`, that recurses without bound.
      Fix: self-exec guard (`test /proc/<pid>/exe -ef bin/simple` → return
      `""`) with in-process fallbacks (`interpret_file`, temp-file interpret
      for `-c`, direct `rt_native_build`). Verified in docker
      (`--pids-limit`): no respawns (proc count stays at 3).
- [~] BUG (follow-up, exposed by the fix): stage-4 cranelift
      `interpret_file` SIGSEGV — two of three root causes fixed 2026-06-10:
      1. [x] Bare `.has()` bound by name-suffix to the only linked
         `*_dot_has` (os.kernel `CapabilitySet.has`) instead of the Dict
         builtin — every dict lookup miscalled. Fixed in
         `codegen/instr/{methods,closures_structs}.rs` (bare `has` →
         tag-dispatched `rt_contains`).
      2. [x] Module-level `var x: [text] = ["lit"]` initializers silently
         dropped (`try_const_array_eval` numeric-only) → nil arrays at
         runtime (`module_path_slot` crash). Fixed:
         `HirGlobalArrayInit.string_values` + `generate_module_init`
         emission (module inits 43 → 49); `_ast_slots_ensure()` guards in
         `ast_part2.spl`.
      3. [x] flat_ast_to_module +6721 root-caused (2026-06-10, commit
         `0bf222e322`): `x = x.push(item)` in expression position stored
         rt_array_push's bool result (raw 1) into the array variable —
         plus three more found in the same pass: first-touch Variable-ID
         collisions for temp locals; module-level struct-literal globals
         silently dropped (now emitted via HirGlobalStructInit in
         module_init); qualified-path `.has` mis-binding via use_map
         suffix fallback + fn-valued struct fields now IndirectCall.
         Stage-4 binary now runs parse → typecheck → monomorphize →
         mode_dispatch.
      4. [x] Sites 5–8 fixed (2026-06-11): SIGSEGV chain fully resolved —
         stage4 runs the whole pipeline in docker with exit 0, zero
         crashes, flat process count. (5) lambda params were stripped by
         `apply_bootstrap_rewrite`'s fn-type→any pass matching lambda
         *expressions* (`fn(m):` became literal `"fn()"` → param `m`
         lowered as nil `GlobalLoad`); fix preserves lambda param lists
         in `pipeline/native_project/compiler.rs`. (6) match-arm leading
         statements dropped by `lower_match_arm_body` — now delegates to
         `lower_do_block`. (7) `for item in dict` lowered as
         array-index over keys — new `rt_for_iterable`/`rt_dict_entries`
         runtime fns yield (k,v) tuples matching interpreter semantics.
         (8) array literal returned from tuple-typed fn read back via
         `rt_tuple_get` → NIL; `rt_tuple_get` now falls back to
         `rt_array_get` for Arrays. Pure-Simple parity verified clean:
         50.mir uses the iterator protocol for non-range for-loops, HIR
         lowers full `arm.body`, and the bootstrap rewrite is seed-only.
      5. [x] 9th site fixed (2026-06-11): not a miscompile — a real
         pure-Simple bug. `get_cli_args` (src/app/cli/main_part1.spl)
         skipped argv[1] whenever it merely `ends_with("main.spl")`
         (meant to skip the CLI's own script path in interpreted mode);
         in the compiled stage4 binary this swallowed user files like
         `h_main.spl` and dropped into the REPL with empty stdin —
         silent exit 0, no output. Fix: precise
         `arg_is_cli_entry_script` predicate matching only
         `*/app/cli/main.spl` / `bootstrap_main.spl` forms. Verified in
         docker (pids-limit 128): stage4 prints "hello stage4" for both
         plain and `*main.spl`-named files, exit 0, flat process count.
         **Stage4 now interprets files end-to-end.** Deploy of the
         self-hosted binary to `bin/simple` remains a separate decision:
         run broader validation (real specs through stage4 in docker)
         before replacing the seed, and follow the smoke protocol
         (setsid + timeout + pgrep, no respawns) on any deploy.
      6. [ ] Broader validation matrix run 2026-06-11 (docker,
         pids-limit 256, vs seed baseline): **NOT green — deploy
         blocked.** Pass: `--version`, file interpretation, flat proc
         count. Fail (10th-site cluster, all new): (a) all 4 real spec
         runs exit 1 with "simple test recursion guard triggered
         (SIMPLE_TEST_DEPTH=1)" — stage4's `test` path re-invokes the
         runner with depth already set; (b) `check src/lib/common/text.spl
         --mode=interpreter` reports "1 error(s) found in 1 of 0
         file(s)" where seed passes (note the 0-files counter); (c)
         `-c 'print(1+1)'` prints a stray `0` line after the correct
         `2`; (d) `lint` hangs past 240s (seed completes; last output
         "workspace-root-guard: OK"). `bin/simple` remains the Rust
         seed until these are fixed and the matrix matches.
         Diagnosis + fixes 2026-06-11 (this session):
         (a) ROOT CAUSE: native `rt_cli_run_tests`
             (runtime/src/value/cli_sffi.rs) spawned
             `current_exe() test ...`; for stage4 that re-enters its own
             `test` dispatch — the child's main_part2 depth guard
             (correctly) refused with DEPTH=1 inherited from the parent's
             env_set. FIX: delegate to `simple_binary_path()` (same
             resolution as lint/check/fmt) + clean error if it resolves
             back to current_exe. Verified seed runs specs green with
             SIMPLE_TEST_DEPTH=1 inherited.
         (b) ROOT CAUSE (miscompile): MIR `HirStmt::For` /
             `lower_for_range` binders resolved the loop variable by
             FIRST name match, but HIR `add_local` appends a fresh slot
             per same-named binding — `for arg in file_args` after
             `val arg` stored elements into the stale slot while the
             body read nil from the new one. check.spl printed
             "ERROR: file not found: {arg}" as a blank line and counted
             "1 of 0 file(s)". FIX: thread the HIR-allocated
             `pattern_local` index through `HirStmt::For` into both MIR
             binders (name search kept only as legacy fallback).
             Regression test:
             mir/lower/tests/basic_lowering.rs
             test_for_loop_var_binds_newest_shadowed_local. NOTE: the
             seed AST interpreter has a SEPARATE same-symptom bug
             (still open) — see
             doc/08_tracking/bug/for_loop_var_shadows_prior_local_binding_lost_2026-06-11.md.
         (c) NOT a stage4 bug: the SEED's `-c` echoes the exit code for
             `print(...)` call form (`should_print_code_result` in
             driver/src/cli/basic.rs only excluded `print ` with a
             space); stage4 only relays the child's output. FIX: treat
             print(/println/eprint/eprintln call forms as non-echoing;
             unit test added. Needs seed redeploy to take effect.
         (d) lint hang: stage4 spins at 99% CPU in-process inside
             `Linter.lint_source` on text.spl (no child, no stdin wait);
             content-dependent (each half of the file lints fine, the
             two halves together hang/crash). Expected to be the same
             for-loop binder miscompile family — re-validate after
             stage4 rebuild with fix (b).
- [ ] After next multi-day parallel-agent session: confirm no recurrence of
      the journal signature (`Activating special unit exit.target` on the
      user manager outside reboots).

## Non-goals

- OS-level prevention of `kill(-1)` — POSIX allows a user to signal their own
  processes; the defense is guards at every kill call site.
- Lint automation for unguarded kills — revisit only if a new incident shows
  the manual rule is insufficient.
