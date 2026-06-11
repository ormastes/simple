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
      5. [ ] Remaining (9th site, silent/semantic — NOT a crash):
         `process_module` (`src/compiler/70.backend/backend/interpreter.spl:38`)
         finds no `fn` named "main" in the self-hosted frontend's HIR
         module for the entry file, returns `Ok(Unit)` without calling
         `call_hir_function` — "hello stage4" never prints. dict.keys()
         and Option `.?` verified working compiled; suspect the
         self-hosted frontend produces an empty or differently-keyed
         `module.functions` for the entry file. Until fixed, self-hosted
         deploys stay blocked and `bin/simple` remains the Rust seed.
- [ ] After next multi-day parallel-agent session: confirm no recurrence of
      the journal signature (`Activating special unit exit.target` on the
      user manager outside reboots).

## Non-goals

- OS-level prevention of `kill(-1)` — POSIX allows a user to signal their own
  processes; the defense is guards at every kill call site.
- Lint automation for unguarded kills — revisit only if a new incident shows
  the manual rule is insufficient.
