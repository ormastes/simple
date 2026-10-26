# Feature Expert — caret_workbench

Caret as a profile of the shared Simple IDE workbench, with smux as the IDE's
general terminal service. Read this before touching `src/app/llm_caret/`,
`src/app/ide/`, or `src/os/apps/smux/` — several of the landmines below cost a
session hours each and are not discoverable from the source.

## Role

Own the process knowledge for making Caret's TUI/GUI, the IDE's terminal
service, and the local-model lane one working product rather than three
independent dashboards.

## Pipeline Links

- [research](../../skill_command/skills/pipe/research/skill.md)
- [design](../../skill_command/skills/pipe/design/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)
- [pipeline next step plan](../../pipeline_next_step_plan.md)

## Feature Links

- Research (design of record):
  [`doc/01_research/app/llm_caret/caret_suite_ide_workbench_smux_migration_2026-09-05.md`](../../../01_research/app/llm_caret/caret_suite_ide_workbench_smux_migration_2026-09-05.md)
  — **source review only; nothing in it was executed.** Its defect IDs
  (CARET-H001/H002, MUX-H001..H006, GUI-H001/H002) are the shared vocabulary.
- Lane state: `.spipe/caret_workbench/state.md`
- Slang local-inference record:
  [`doc/08_tracking/bug/caret_slang_local_inference_provider_missing_2026-08-21.md`](../../../08_tracking/bug/caret_slang_local_inference_provider_missing_2026-08-21.md)
- Source: `src/app/llm_caret/`, `src/app/ide/`, `src/app/editor/`,
  `src/os/apps/smux/`, `src/lib/gc_async_mut/slang/`

## The shared contract — import it, do not re-derive it

`src/app/llm_caret/workbench/session_contract.spl` is the single session type
surface for the TUI, the GUI, the IDE terminal service, and the Caret lifecycle
adapter. It exists so those lanes cannot each invent a session notion and then
disagree at the seam.

Two rules it encodes:

1. **Identity is `(value, generation)`** — never a row index, a bare PID, or a
   display name. A restarted agent keeps its id and bumps its generation, so a
   message captured against the old generation is REFUSED rather than landing in
   the replacement. `same_session` requires both halves.
2. **The four state axes are independent**: `ProcessLifecycle`, `AgentTurn`,
   `Transport`, `CapabilityEvidence`. A live process is not a working agent; a
   dropped transport is not an exited child; a declared capability is not a
   verified one. Collapsing them is exactly how a UI reports `Connected` over a
   session that never handshook (GUI-H001).

`ComposerDraft` binds its target at capture time — switching the selected agent
must not redirect an in-flight draft. `draft_targets(draft, live)` is the check.

Probe-verified on the Sep-5 seed (`build/nb/fixtures/probe_contract.spl`):
`same_after_restart=false`, `stale_draft_targets_new_gen=false`,
`draft_targets_own=true`.

## Host landmines (measured 2026-09-05, this mac)

- `bin/simple` is a **bootstrap Rust seed**. It has no `run`/`test`. The working
  runner is `src/compiler_rust/target/bootstrap/simple run <file.spl>`.
  `bin/simple test` is LOAD-ONLY here.
- **Module resolution is file-relative.** A probe in `/tmp` fails with
  `module path segment 'app' not found` even though the module is fine. Put
  fixtures in `build/nb/fixtures/`.
- The `run` verdict grammar is `N examples, M failures` — **not** `Results:`,
  which is the `test` grammar. The runner emits the singular `1 failure`, so
  match substrings.
- **PTY is NOT usable — do not plan a terminal on it.** An early read of this
  tree concluded "the externs are backed, so smux gets real terminals under the
  seed". That was WRONG and it was corrected by measurement on 2026-09-05.
  Three independent problems:
  1. Only `rt_pty_open` and `rt_pty_spawn` are registered in the interpreter
     extern table (`interpreter_extern/mod.rs:2803-2804`). `rt_pty_read` and
     `rt_pty_write` are registered nowhere, so they resolve to
     `E-SFFI-001 unknown extern function` and silently return nil.
  2. `rt_pty_spawn` returns `-1` on this host even with two fresh fds.
  3. The declarations in `smux_remote.spl:22-30` DISAGREE with the definitions
     in `pty.rs`: fd is `i32` vs `i64`, and the second parameter is `buf_size`
     vs `timeout_ms`. So even once registered, the calls are wrong.

  What actually works, and what smux now uses: **real child processes over
  pipes**, via `std.nogc_sync_mut.io.process_ops` (no raw `rt_*`). That
  satisfies a real-child nonce oracle. It gives no controlling terminal, so
  job control and full-screen TUI passthrough remain out of reach.
  Record: `doc/08_tracking/bug/pty_externs_unusable_under_seed_interpreter_2026-09-05.md`.
- **A module-level `var` write is silently discarded when the RHS method reads
  `me`.** `_svc = _svc.add_session(...)` loses the write. Workaround:
  `val cur = _svc; _svc = cur.add_session(...)`. This had already left
  `smux_api_spec` 4-of-5 RED before any workbench change. Tracked RED spec:
  `test/01_unit/compiler/module_var_write_lost_when_rhs_reads_me_spec.spl`.
- An extern with no runtime backing **silently returns nil** in this repo.
  Verify backing before trusting any new `rt_*` result.
- **Never `git stash` in this working copy.** It is shared with peer sessions and
  the stash stack is global. Measured 2026-09-05: a lane's `git stash` failed to
  create (blocked by a conflicting untracked entry), and its `git stash pop` then
  tried to apply an unrelated stash belonging to ANOTHER session. It aborted with
  "stash entry kept" and nothing was lost — but only because the conflict check
  caught it. Use a copy, not the stash stack.
- **`var row = outer[1]` on a nested array copies**, and writes through the
  binding are silently discarded. Chained `outer[0][1] = x` and top-level
  `flat[1] = x` both work. See
  `doc/08_tracking/bug/nested_array_element_bound_to_var_copies_2026-09-05.md`;
  the workbench TUI grid uses a flat row-major `cells: [text]` because of it.

- **Inexplicable "symbol not found" / orphaned helper: diff against
  `git show e274cd33719^:<file>` before anything else.** That merge commit
  clobbered spec preambles and live code across lanes (llm_caret 138/157 ->
  157/157 once restored, `2796fe9a93c`). Full note:
  [llm_caret_messaging](../llm_caret_messaging/skill.md) § Landmines.

## slang local model on macOS

The local path is GGUF through ggml
(`src/runtime/slang_ggml_shim.c`, int64-only ABI, dynamic SFFI, behind
`model_executor/backend.spl`). It generated real text on a DGX Spark on
2026-09-04. On macOS:

- `scripts/check/build-slang-ggml-shim.shs` is **Linux-only** as written: it
  defaults `LLAMA_ROOT=/home/yoon/dev/llama.cpp` and hard-requires
  `build/bin/libllama.so`. macOS builds `libllama.dylib` (confirmed — the
  llama.cpp build here produced `libggml-*.dylib` plus a Metal backend).
- Model discovery walks **directories**: `scan_model_root` /`describe_model` in
  `model_executor/model_loader/native_formats.spl`. Layout is
  `<SLANG_MODEL_ROOT>/<model-name>/<file>.gguf`, not a bare file in the root.
- `curl`/`wget` are blocked by a project hook. Model bytes come via `git lfs`.
- **Acceptance is generated tokens through `caret --provider slang_local`**, read
  from the last stdout line of
  `scripts/check/check-slang-ggml-inference.shs`. A load, a `--version`, or
  "the model was found" is not evidence.

## Evidence rules specific to this feature

- "Check TUI rendering" means a **captured cell grid** written under
  `build/test-artifacts/` and asserted against the renderer's output — model it
  on `test/02_integration/app/ide/ide_feature_check_integration_spec.spl`. A
  source grep is not a capture.
- Source-text assertions are banned here and have burned this area before: a
  spec that asserts a file *contains* a symbol name passes while the function
  returns `[]` or is never called.
- A preview card never resizes the provider's PTY to the card's size. One
  canonical parser/screen model per terminal; previews consume snapshots.

## Update Rule

When research, requirements, architecture, design, tests, implementation,
verification, or release artifacts change for this feature, update this file
with the new links and current handoff notes — in the same commit as the work,
per `.claude/rules/vcs.md`.
