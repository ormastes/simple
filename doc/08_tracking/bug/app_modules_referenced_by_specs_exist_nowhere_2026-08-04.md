# Three app modules/symbols their specs import exist nowhere in the tree

- Status: PARTIALLY-RESOLVED (2026-09-12) — 3 of the 4 specs green; see Triage 2026-09-12
**Found:** 2026-08-04
**Severity:** high — 19 spec examples cannot run, and two of the three are real
CLI surfaces (`simple os …`, `simple build --target-feature …`) that a user can
invoke today and get nothing back

## Symptom

| Spec | Verdict | Runner error |
|---|---|---|
| `test/01_unit/app/build/feature_flags_spec.spl` | 0 passed, 1 failed | `semantic: Cannot resolve module: app.build.feature_flags` |
| `test/01_unit/app/build/opt_remarks_spec.spl` | 0 passed, 1 failed | `semantic: Cannot resolve module: app.build.opt_remarks` |
| `test/01_unit/app/cli/cli_os_spec.spl` | 0 passed, 7 failed | `semantic: function `handle_os_inline` not found` (×7) |
| `test/01_unit/app/cli/os_build_dispatch_spec.spl` | 0 passed, 1 failed | source-text assertion on `handle_os_build_inline` |

Repro for the first two:

```sh
SIMPLE_TIMEOUT_SECONDS=0 bin/simple test test/01_unit/app/build/feature_flags_spec.spl
```

Expected: the module resolves. Actual: `Cannot resolve module`.

## Root cause (each PROVED separately)

**1 & 2 — `app.build.feature_flags` / `app.build.opt_remarks` were never
committed.** `src/app/build/` holds exactly one file, `cli_entry.spl`.
`git log --all -- src/app/build/feature_flags.spl` lists commits, but
`git cat-file -s $(git rev-parse <c>:src/app/build/feature_flags.spl)` fails with
*"path does not exist"* on every one of them — the paths are only touched by
deletions, never added. The APIs the specs import
(`parse_target_features`, `apply_feature_overrides_x86/_aarch64/_rv64`,
`FeatureFlag`; `parse_opt_remarks`, `opt_remark_config_disabled`,
`emit_cipher_remark`, `emit_cipher_remark_if`, `OptRemarkConfig`) return **zero
hits** from `/usr/bin/grep -rn 'fn parse_target_features\|fn parse_opt_remarks\|fn
emit_cipher_remark' src/ --include=*.spl`. The specs' own `use
compiler.backend.feature_caps.{X86Caps, Aarch64Caps, Rv64Caps}` import *does*
resolve, so the specs were written against a real design that only ever landed
on the compiler side.

**3 — the SimpleOS CLI wrapper was dropped by the `_CliMain` split.**
`src/app/cli/main.spl` is now 17 lines that `export use
app.cli._CliMain.args_and_os_commands.*`, and that module (388 lines) contains
**no `handle_os_*` function at all** despite the name. The four handlers
(`handle_os_build_inline:271`, `handle_os_run_inline:314`,
`handle_os_test_inline:368`, `handle_os_inline:426`) last existed in
`src/app/cli/main_part1.spl` at `6a45d1b6efa` (2026-07-31), and
`git merge-base --is-ancestor 6a45d1b6efa HEAD` answers **NO**.

## Why not fixed now

For 1 & 2 this is new feature work, not a restore: there is no prior
implementation to recover, so writing `app.build.feature_flags` means designing
the x86/aarch64/rv64 override semantics from the spec's assertions alone, which
is exactly the kind of guess that produces a green test over a wrong
implementation.

For 3 the recoverable copy is **stale against its own spec**: `6a45d1b6efa`
writes `val target = get_qemu_target(arch.unwrap())`, while
`test/01_unit/app/cli/os_build_dispatch_spec.spl:11-12` asserts the source
contains `val target = get_target(arch_value)`. So the spec was written against a
*newer* revision than the one that survives, and a straight restore would still
leave `os_build_dispatch_spec` red while adding ~200 lines whose transitive
dependencies (`os_parse_log_arg`, `os_log_arg_error`, `os_parse_scenario_arg`,
`get_scenario`, `build_scenario`, `arch_from_name`, `get_qemu_target`,
`build_os`, `_export_os_log_mode_inline`, `_restore_os_log_mode_inline`) are
themselves absent and touch the SimpleOS/QEMU build path.

## Triage 2026-09-12

Binary: `bin/simple` = shared clone's Rust seed, `sha256 3d120a6f…`, aarch64.

Re-ran all four specs from the symptom table.

| spec | 2026-08-04 | now |
|---|---|---|
| `test/01_unit/app/build/feature_flags_spec.spl` | 0 passed, 1 failed | **OK 17/17** — module landed since |
| `test/01_unit/app/build/opt_remarks_spec.spl` | 0 passed, 1 failed | **OK 13/13** — module landed since |
| `test/01_unit/app/cli/cli_os_spec.spl` | 0 passed, 7 failed | 6/7 (was `handle_os_inline` not found ×7) |
| `test/01_unit/app/cli/os_build_dispatch_spec.spl` | 0 passed, 1 failed | **OK 1/1** |

Rows 1 and 2 were fixed by other work; rows 3 and 4 are fixed here.

`handle_os_inline` / `handle_os_build_inline` now exist in
`src/app/cli/_CliMain/args_and_os_commands.spl` (re-exported by
`app.cli.main`), so the unified CLI dispatches `os` without delegating to a
separate entry file. `handle_os_build_inline` deliberately uses `get_target`
(the per-platform kernel SMOKE lane) rather than `get_qemu_target` (the
filesystem-backed ACCEPTANCE lane), which is what
`os_build_dispatch_spec.spl` pins; validation rejects a bad `--log`, a bare
`--arch`/`--target`/`--scenario`, an unknown scenario and an unknown
architecture before `SIMPLE_OS_LOG_MODE` is ever exported, so a rejected
command leaves the caller's environment byte-identical (the spec asserts this).
Everything else delegates to the existing `os.cli.handle_os`; nothing was
duplicated.

Blast radius checked — the other three specs that import `app.cli.main` are
unaffected: `cli_helpers_cycle_spec` 1/1, `cli_unknown_subcommand_exit_code_spec`
4/4, `static_startup_fast_path_spec` 3/3.

**The one remaining failure is NOT this bug.** `cli_os_spec`'s "dispatches os
targets successfully" now fails with
`semantic: unknown variant or method 'Riscv64' on enum Architecture`, which is
the bare-name registry collision tracked in
`bare_name_registry_collision_trigger_conditions_2026-07-30.md`. Widening the
CLI's module graph to reach `os.cli` pulled a second `enum Architecture` into
the same flat name registry. That record was open precisely because five lanes
failed to reproduce the collision; a 10-line reproducer derived from this
failure is recorded there today.
