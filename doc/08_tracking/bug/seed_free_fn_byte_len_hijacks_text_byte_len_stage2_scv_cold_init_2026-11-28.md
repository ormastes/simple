# Seed-built Stage 2: a free `fn byte_len` in the closure hijacks every `text.byte_len()`

Status: source workaround landed (rename + reason-bearing refusal), verified on
reduced native probes built by the pinned `c6e3ee3c112` seed. NOT yet confirmed
by a full Stage 2 bootstrap. The seed mangler defect itself is OPEN.

- **Severity:** P1 (every aarch64 Stage 2 candidate refused cold SCV admission)
- **Area:** Rust seed native-project mangler; `src/os/kernel/loader/byte_utils.spl`
- **Workaround site:** `src/os/kernel/loader/byte_utils.spl` (`lb_byte_len`, tagged `# @workaround bug=...`)
- **Shard:** `doc/08_tracking/bug/db/seed_free_fn_byte_len_hijacks_text_byte_len_stage2_scv_cold_init_2026-11-28.sdn`
- **Spec:** `test/01_unit/app/compiler_entrypoint/inventory_refusal_reason_spec.spl`

## Symptom

`--full-bootstrap --stop-after-stage2` pinned at `c6e3ee3c112` (aarch64) aborted
at Stage 2 sanity with `candidate_frontend_smoke: scv-prime-inventory failed
(raw rc=1)`. The `.scv-prime` log held only:

```
[coordinator-route] per-file worker pool + per-module link
[scv] cold-init scan start lines=102871
SCV-E-ADMISSION: git-event-refresh-failed
```

Pins at `f3cf72db429` and `f43f68c218e` passed the same step.

## Root cause

Two causes, and only the second is in the regression range.

1. **Latent seed defect (predates the range).** The seed-built binary calls a
   free user `byte_len` for a text `x.byte_len()` in a module that never
   imports it. The rebinding site inside the seed was NOT isolated (see Open).
   `src/os/kernel/loader/byte_utils.spl` declared the only free
   `fn byte_len(data: [u8])` in the tree, so once that module is in a closure
   every `x.byte_len()` on a text in the WHOLE closure is rebound to it. The
   module that calls it does not have to import it.
2. **Trigger: `bf0dc71aaf8` (PR #12182, W5-2).** It wired
   `app.cli.bootstrap_driver_provider_client_v1` into
   `src/app/cli/bootstrap_main.spl`. That import reaches `os.smf.provider_loader`
   -> `os.posix.dynlib` -> `os.posix.dylib_async` ->
   `os.kernel.loader.dylib_registry` -> `elf_loader` / `smf` -> `byte_utils`.

On arm64 the hijacking body is `rt_arm_array_len_u32(data)`, which reads 0 for
a text. `line.byte_len() <= 2` in the cold-init row walk
(`src/app/compiler_entrypoint/inventory_events.spl`) then refused the first row
(`H examples/10_tooling/README.md`). On x86_64 the body is `data.len()`, which
happens to be right for ASCII text, so the defect is silent there.

## Evidence (2026-11-28, aarch64)

- Rerunning the scv-prime command with the pinned `c6e3` candidate in a fresh
  `c6e3` worktree reproduces in 0.5 s; the `f3cf` candidate on the same tree
  scans normally. Binary, not tree.
- `objdump` of `..._compiler_inventory_git_events_traced_cost_v1` in the `c6e3`
  candidate calls `os__kernel__loader__byte_utils__byte_len`; the `f3cf`
  candidate does not. The `c6e3` candidate has 1028 call sites of that symbol
  and 42 `os__*` text symbols; the `f3cf` candidate has none.
- gdb: `_compiler_inventory_event_for_path_cost_v1` is never entered, so the
  refusal is the row-shape check on row 1.
- Direct probe (both seeds, `native-build --backend llvm`): with
  `use os.kernel.loader.byte_utils.{lb_read_u8}` in the file,
  `"H examples/10_tooling/README.md".byte_len()` prints 0. The `f3cf` seed
  prints 0 too, which is what makes cause 1 pre-existing.
- Scope probe (pinned `c6e3` seed, fixed tree): an entry file that declares its
  own `fn byte_len(data: [u8]) -> i64: 0` and calls the cold-init refresh.
  The entry module itself still reads `byte_len=31`; `inventory_events.spl`,
  which does not import it, is hijacked and refuses with
  `git-event-refresh-failed:row-shape:byte_len=0:H examples/10_tooling/README.md`.
  So one free `byte_len` anywhere in the closure is enough, and the new reason
  text is what a compiled candidate prints.
- Chain probe (pinned `c6e3` seed, entry importing the provider client and
  calling `compiler_inventory_refresh_v1(.., cold_init = true)`):
  pre-fix tree prints `byte_len=0` and `reason=[git-event-refresh-failed]`;
  the fixed tree prints `byte_len=31` and publishes the inventory.

## Fix

- `byte_len` in `byte_utils.spl` is renamed `lb_byte_len` (all six `@cfg`
  variants, its two internal callers, `fs_exec_spawn.spl`, and
  `test/01_unit/os/kernel/loader/byte_utils_spec.spl`). No free `byte_len`
  remains in the tree, so the seed has no candidate to bind.
- The refusal names its reason. `_compiler_inventory_git_events_traced_cost_v1`
  returns `Result<CompilerInventoryGitEventsV1, text>`, and the admission error
  becomes `git-event-refresh-failed:<branch>:<detail>`; the row-shape reason
  carries the measured byte length (`row-shape:byte_len=0:H examples/...`), so
  this class is self-evident the next time it happens.

## Open

- Seed fix not attempted here; it needs a seed rebuild to verify. The rebinding
  site is not isolated. Candidates, all in
  `src/compiler_rust/compiler/src/pipeline/native_project/mangle.rs`:
  `resolve_method_call_static` resolving through `resolve_name_variants` (a
  free function leaking into the import map as a bare entry, the documented
  `char_at` class), or the exact-lone-candidate arm of
  `resolve_unbound_by_suffix`. `resolve_method_call_static` already returns
  early for a list of string builtins (`starts_with`, `trim`, `char_at`, ...);
  `byte_len` and `char_count` are not on it, which is the candidate fix. Free
  calls `byte_len(data)` go through `resolve_call_target` and must keep binding
  (`exact_user_byte_len_candidate_still_binds`). Retire the `@workaround` tag
  once a seed fix lands and a Stage 2 rebuild confirms it.
- `byte_utils.spl` also declares a free `byte_at`. The `c6e3` candidate carries
  no `byte_utils__byte_at` symbol, so it is not hijacked today; it is the same
  exposure.
- A full `--full-bootstrap --stop-after-stage2` run is still needed to prove the
  Stage 2 gate passes.
