# SOSIX Host-Interface-Only Plan

**Date:** 2026-09-18
**Status:** Planned. Lane H1 is done in this change. Lanes H2 to H9 are open.
**Parent plan:** `doc/03_plan/agent_tasks/sosix_runtime_unification_parallel_plan_2026-09-05.md`
**Design:** `doc/05_design/runtime/sosix_runtime_unification_design.md`
**Lane state:** `.spipe/sosix_runtime_unification/state.md`
**Request:** "Refactor the host interface so it goes through the SOSIX interface only. The plan is not done, or it is broken again. Check it, fix it, and add a plan."

**Target rule.** Library and app code reaches the host (fs, time, process, env, net) only through
SOSIX contracts, which are `std.nogc_async_mut.sosix.*` and `std.common.contracts.sosix.*`.
A direct `rt_*` host call or `extern fn rt_*` declaration may appear only in an allowlisted
provider file: `scripts/check/no_direct_rt_allowlist.txt`, plus the SOSIX capsule itself. Every
other site is debt, and a ratchet counts it (§4).

All measurements used the deployed seed `bin/release/aarch64-unknown-linux-gnu/simple`, with
sha256 prefix `3d120a6f9ab5704b`, 50,093,192 B, and mtime 2026-09-06 09:59. This is the same binary that
state.md recorded on 2026-09-06, so no result below comes from a binary change. The worktree was
`work/sosix-host-interface-only` at `c3927751dc1`, compared against the lane commit `4bd22ad051f`
in a detached worktree.

## 1. Health check: status of the 2026-09-05 plan

Each spec was run once with `bin/simple test --no-session-daemon <path>`. That covers 81 files
matching `*sosix*_spec.spl` plus the capsule and contract spec directories.

| Row / spec | 2026-09-05 claim | 2026-09-18 result | Verdict |
|---|---|---|---|
| A1 `operation_core_spec`, `fs_completion_pump`, `fs_registered_buffer_client_v1`, `fs_async_client_v1` | green | green | holds |
| A2 `service_ids_spec`, A3 `error_spec` | 3/3, 3/3 | green | holds |
| B2 `fs_async_spec`, B3/B5 `fs_sync_spec`, `file_driver_spec`, B4 `time_spec`, `host_facade_spec` | green | green | holds |
| G2 `io_spec` (both trees) | 9/9 | green | holds |
| Wait-set `completion_wait_set_spec` | 5/5 | green | holds |
| H2 `test/05_perf/lib/sosix_hosted_fs_perf_spec.spl` | 2/2 | green | holds |
| AC acceptance `sosix_runtime_unification_acceptance_spec` | 8/8 | **7/8, fixed to 8/8** | **broken since landing**. The AC-5 example reads `doc/10_metrics/runtime/sosix_unification_{perf_report,baseline}_2026-09-05.md`. Lane commit `4bd22ad051f` never committed either file. They existed only as untracked files in the main worktree and in the unmerged commit `2f5261a96a4` (branch `codex/opt-g0-20260910`). Restored byte-identical in this change. |
| C2 `posix_spec` | 3/3 on the private seed only | 0/3, `unknown extern function: rt_fd_pread` | expected. The deployed seed predates the externs (state.md, 2026-09-06 10:02). Not a regression. |
| H1 `check-sosix-capsule-boundaries.shs` | PASS (src=6238, ceiling 6240) | **FAIL**, R5 src=6307 (6303 after H1) > 6240 | **regressed by other lanes** (§1.1) |
| `push-no-direct-rt` (mandatory push tier, `--roots src`) | PASS | **FAIL 6307 > 6306**, then PASS 6303 after H1 | **origin/main red by one site**, fixed here (§1.1) |
| `fs_ipc_codec_v1_spec` (listed as a pre-existing red) | 4/6 | green | improved |
| `fs_service_vfs_backend_v1_spec`, `fs_service_adapter_v1_spec` 4/6 | pre-existing red | identical | unchanged |

The other 31 non-green specs (29 reds and 2 child timeouts) are all kernel or OS-side specs under `test/{01_unit,unit}/os/sosix/`,
`test/{01_unit,unit}/os/kernel/ipc/`, `test/{03_system,system}/app/os/feature/`, and
`test/03_system/os/qemu/`. They are outside the capsule and outside the lane's edit set. Every
one of them gives the same pass/fail count at `4bd22ad051f` as at HEAD, so none is a
regression. The families are:

- **Module-level fixed-array globals do not resolve in the seed.** The error is `variable
  sosix_dataset_active / sosix_fd_own_active / sosix_queue_recv_notif_id not found`. It affects
  `share`, `share_api`, `dataset_vfs`, `fd_ownership`, `queue_notify`, and `sosix_process_sharing`.
  The sources were last touched in `e274cd33719` (2026-08-27).
- **Specs are ahead of their implementation.** Examples: `SOSIX_FS_IPC_MAX_REGISTERED_BUFFER_BYTES_V1`,
  `sosix_qemu_v2_structural_admission_parse`, `host_wm_render_backend_key_from_configuration`,
  and `SyscallId.FsPreadRegisteredV1`, none of which is defined in `src`.
- **`syscall_sosix_share_spec` fails to load.** `src/os/kernel/abi/syscall_shim_positioned.spl:21`
  imports `sosix_fs_kernel_uninstalled_positioned_state_v1`, but
  `src/os/sosix/fs/kernel_positioned_dispatch_v1.spl` exports only
  `sosix_fs_kernel_positioned_state_v1(owner)`. The API drift predates the lane. The failure
  looks different now: the lane ran 9 examples that all failed, and HEAD executes none. The
  cause is the same.
- **Child timeouts at the 120 s budget:** `positioned_filesystem_backends_spec` and
  `positioned_backend_composition_v1_spec`.

### 1.1 Direct-rt drift

| Rev | `--roots src` forbidden | Baseline file |
|---|---|---|
| `4bd22ad051f` (lane, 2026-09-05) | 6234 | 7776 |
| `ba7626d2508` (2026-09-07 tighten) | 6072 | 6072 |
| `e87e884048a` (2026-09-15) | 6306 | **6306**. It was raised by 234 inside the commit titled "test: fix easy spec failures". This loosened the ratchet without a stated reason. |
| `05acf20552b` (#1052, 2026-09-17) | 6307 | 6306, so the blocking push gate is red. The +1 is `rt_dict_contains` in `src/compiler/20.hir/hir_lowering/_Items/module_build.spl`. |
| this change (H1) | **6303** | 6306, so the gate is green again |

The net +73 between the lane commit and HEAD comes from 491 sites added and 418 removed. The
largest additions are in `src/plugins/backend_llvm_lib/llvm_lib_translate_expr.spl` (+47, a
move out of `70.backend`), `src/compiler/80.driver/cache/shared_generation_store.spl` (+44) and
`src/lib/nogc_sync_mut/storage_roots/publisher.spl` (+16), both from `e0fa5ef45e2` (#319), and
`src/lib/common/cache_{daemon_,}host_authority_v1.spl` (+72, cache L7/L8 lane `920b7c2dcb3`
and its predecessors). This plan does not raise the capsule gate's hard-coded 6240. Lane H7 settles it.

## 2. Host-access census (2026-09-18, before H1)

Scope: `src/lib/**` and `src/app/**` `*.spl`, excluding `vendor/`, every prefix in
`no_direct_rt_allowlist.txt`, and the SOSIX capsule and contracts. A site counts when a line
that is not a comment contains `rt_<family>...(`. The families are:

- fs: `file|fd|dir|path|fs|mkdir|rmdir|unlink|rename|stat`
- time: `time|clock|sleep|monotonic|now`
- process: `process|proc|spawn|exec|exit|getpid|kill|pipe|pty`
- env: `env|getenv|setenv|cwd|chdir|args`
- net: `tcp|udp|socket|net|http|dns|sock`

`decl` is an `extern fn` line, and `call` is any other line.

```sh
/usr/bin/grep -rnE --include='*.spl' '^[^#]*\brt_(file|fd|dir|path|fs|mkdir|rmdir|unlink|rename|stat|time|clock|sleep|monotonic|now|process|proc|spawn|exec|exit|getpid|kill|pipe|pty|env|getenv|setenv|cwd|chdir|args|tcp|udp|socket|net|http|dns|sock)[a-z0-9_]*\(' src/lib src/app | grep -v /vendor/
# then drop allowlisted prefixes and src/lib/{nogc_async_mut/sosix,common/contracts/sosix}/
```

| Subsystem | Calls | Decls |
|---|---|---|
| fs | 560 | 282 |
| process | 184 | 98 |
| time | 106 | 36 |
| net | 56 | 34 |
| env | 40 | 37 |
| **Total** | **946** (lib 358, app 588) | **487** |

266 files are involved. H1 removed 4 calls and 2 decls, which leaves 942 calls and 485 decls.

**Calls by top-level directory:** `src/lib/nogc_sync_mut` 192, `src/app/io` 119, `src/app/editor` 102,
`src/app/snpm` 57, `src/lib/gc_async_mut` 44, `src/lib/nogc_async_mut` 41, `src/lib/common` 26,
`src/app/test_daemon` 25, `src/lib/editor` 22, `src/app/test` 21, `src/app/test_runner_new` 19,
`src/lib/scv` 16, `src/app/doc` 16. The remaining directories have 14 or fewer each.

**Where each subsystem is concentrated:**

| Subsystem | Directories with the most calls |
|---|---|
| fs | `lib/nogc_sync_mut` 102, `app/editor` 80, `app/snpm` 46, `app/io` 40, `lib/nogc_async_mut` 26 |
| process | `app/io` 71, `lib/nogc_sync_mut` 30, `lib/editor` 19, `app/editor` 17, `app/snpm` 9 |
| time | `lib/gc_async_mut` 33, `app/test_daemon` 21, `app/test` 16, `lib/nogc_sync_mut` 9 |
| net | `lib/nogc_sync_mut` 37, `app/devhub` 10, `app/itf` 6 |
| env | `lib/nogc_sync_mut` 14, `lib/nogc_async_mut` 8, `app/io` 6 |

**Most-called symbols:** `rt_file_exists` 135, `rt_file_read_text` 125, `rt_file_write_text` 57,
`rt_time_now_unix_micros` 48, `rt_process_run` 42, `rt_time_now_micros` 37, `rt_env_get` 22,
`rt_path_absolute` 21, `rt_dir_exists` 21, `rt_http_request` 17.

**Top 20 files by total sites (calls + decls):**

| File | Sites |
|---|---|
| `src/lib/nogc_sync_mut/io_runtime.spl` | 84 |
| `src/lib/nogc_sync_mut/io/http_sffi.spl` | 48 |
| `src/app/io/jit_sffi.spl` | 31 |
| `src/lib/nogc_async_mut/io/mod_stub.spl` | 28 |
| `src/lib/nogc_sync_mut/storage_roots/publisher.spl` | 25 |
| `src/lib/scv/compile_source_inventory.spl` | 24 |
| `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl` | 20 |
| `src/app/io/process_ops.spl` | 20 |
| `src/app/io/minimal_runtime_ops.spl` | 20 |
| `src/app/io/bootstrap_adhoc_ops.spl` | 20 |
| `src/app/editor/editor_controller.spl` | 20 |
| `src/lib/editor/services/debug_session_dap.spl` | 18 |
| `src/app/test_runner_new/test_runner_single.spl` | 17 |
| `src/app/editor/mcp_tools_helpers.spl` | 17 |
| `src/app/editor/editor_ctrl_wiki.spl` | 17 |
| `src/app/io/vhdl_sffi.spl` | 16 |
| `src/app/io/vhdl_ffi.spl` | 16 |
| `src/lib/nogc_sync_mut/fs.spl` | 14 |
| `src/lib/nogc_sync_mut/database/atomic.spl` | 14 |
| `src/lib/nogc_async_mut/fs.spl` | 14 |

**Reading the census.** Several of the top files are the host boundary itself, not consumers of
it: `io_runtime.spl`, `io/http_sffi.spl`, `app/io/*_sffi.spl`, `app/io/process_ops.spl`, and
`nogc_async_mut/io/mod_stub.spl`. Migrating their sites would only move the host boundary.
Instead, lane H8 either classifies them as providers (allowlist) under SOSIX or folds them into
the capsule. The migration targets are ordinary consumers such as `app/editor`, `app/snpm`,
`app/test_daemon`, `lib/editor`, `lib/scv`, and the browser renderer.

**Gaps in the facade.** Today the SOSIX facade covers only the following:

- process run, spawn, kill, is-running, and which
- pty
- the platform family
- the monotonic clock
- positioned fd I/O

It has no wall clock (`rt_time_now_unix_micros`, 48 calls), no env get (`rt_env_get`, 22), no
path-level file exists/read/write (317 calls), and no HTTP. Consumers cannot migrate until
those leaves exist, which is why lanes H3 to H5 come first.

## 3. Done in this change: lane H1, the process leaf in `app/jj`

- `src/app/jj/status.spl` and `src/app/jj/diff.spl` no longer declare
  `extern fn rt_process_run`. They import `std.nogc_async_mut.sosix.host_facade.{sosix_run}`
  directly. They do not use the package `__init__`, so the unbacked POSIX leg stays out of the
  jj CLI's import chain. This removes 4 call sites and 2 declarations.
- New spec `test/01_unit/app/jj/jj_sosix_host_route_spec.spl`:
  - Red before the change: 3/4. The structural example failed on `extern fn rt_process_run`.
  - Green after the change: 4/4.
  - The three behaviour examples compare each wrapper with `sosix_run` running the same `jj`
    command, so they hold whether or not `jj` is installed.
  - `jj_log_numeric_guard_spec` stays 1/1.
  - `bin/simple run src/app/jj/main.spl status` prints `Error running jj status:` and exits 255
    both before (lane worktree) and after. `jj` is absent on this host.
- Gates:
  - `check-no-direct-rt --roots src` went from FAIL 6307 to PASS 6303.
  - `check-sosix-capsule-boundaries` still fails on R5 only (6303 > 6240, see H7). R1 to R4 are
    clean.

## 4. Ratchet: extend the existing gates, add no new one

- **R5 single source.** `check-sosix-capsule-boundaries.shs` stops hard-coding `SRC_CEILING=6240`.
  Instead it reads `scripts/check/no_direct_rt_baseline.txt`, and optionally keeps a tighter
  lane ceiling with a dated debt note. Two ceilings that disagree (6240 vs 6306) are the
  reason one gate is red while the other is green.
- **R6 host-family ratchet (new rule in the same script).** R6 counts the §2 census population
  (fs/time/process/env/net, `src/lib` and `src/app`, allowlist and capsule excluded), split by
  family. It fails when any family rises above the baseline in
  `scripts/check/sosix_host_access_baseline.txt`. The script already fails closed and already
  runs `--selftest`. R6 adds one good fixture and one bad fixture.
- **Baseline hygiene.** A change to either baseline file must be its own commit, and the commit
  message must state the measured count. The 6072 → 6306 raise inside a test-fix commit is the
  pattern R6 must not repeat.
- The manifest row `push-sosix-capsule-boundaries` stays advisory until R5 and R6 are green on
  `origin/main`. After that, promote it to blocking.

## 5. Parallel lanes

| Lane | Owns (exclusive) | Deps | Work | Evidence | Model |
|---|---|---|---|---|---|
| H1 | `src/app/jj/**`, `test/01_unit/app/jj/jj_sosix_host_route_spec.spl` | none | Route `rt_process_run` through `sosix_run` | **DONE**, see §3 | haiku-ok |
| H2 | `src/app/snpm/**`, `src/app/gen_lean/main.spl`, `src/app/linkers/main.spl`, `src/app/exp/main.spl`, `test/01_unit/app/snpm/*sosix*` | none | Route the remaining `rt_process_run` consumers (about 12 calls) through `sosix_run` | Parity spec as in H1. `check-no-direct-rt --roots src` count goes down. | haiku-ok |
| H3 | `src/lib/nogc_async_mut/sosix/time.spl`, `test/01_unit/lib/nogc_async_mut/sosix/time_spec.spl` | none | Add the wall-clock leaf `sosix_time_wall_unix_us()` over `std.nogc_sync_mut.io.time_ops`. Add no new extern. | `time_spec` gains an example, red then green | haiku-ok |
| H3b | `src/app/test_daemon/**`, `src/app/test/bench/**` | H3 | Migrate the `rt_time_now_unix_micros` consumers (about 26 calls) | Existing test_daemon specs stay green. The count goes down. | haiku-ok |
| H4 | `src/lib/nogc_async_mut/sosix/host_facade.spl`, `host_facade_spec.spl`, and the `rt_env_get` consumers in `src/app/editor/**` | none | Add `sosix_env_get` (an alias of `std.nogc_async_mut.env`, not a new extern). Migrate the editor env sites. | `host_facade_spec` gains an example. The editor specs stay green. | sonnet |
| H5 | new `src/lib/nogc_async_mut/sosix/host_fs.spl`, `__init__.spl`, `doc/05_design/runtime/sosix_runtime_unification_design.md` §4 | none | Design decision: a path-level fs leaf (exists/read/write/delete/dir) that re-exports `std.nogc_sync_mut.io_runtime` typed aliases. Choose alias or adapter per design §4.2. File size is capped at 300 lines. | New `host_fs_spec`. Capsule R1 to R4 stay clean. | sonnet |
| H5a | `src/app/editor/**` except the env sites H4 owns | H4, H5 | Migrate 80 fs calls | Editor specs stay green. The fs family count drops by at least 80. | sonnet |
| H5b | `src/lib/editor/**`, `src/lib/scv/**` | H5 | Migrate fs and process calls (about 38) | Existing specs stay green | sonnet |
| H6 | `src/lib/gc_async_mut/gpu/browser_engine/**` | H3 | Migrate the time family (33 calls) | Browser-engine specs stay green | haiku-ok |
| H7 | `scripts/check/check-sosix-capsule-boundaries.shs`, new `scripts/check/sosix_host_access_baseline.txt`, `config/check/must_check_gates.sdn` row `push-sosix-capsule-boundaries` | H8 | Apply §4: R5 reads the shared baseline, and R6 becomes the family ratchet | `--selftest` passes with 4 fixtures. The gate PASSes on the lane tip. | sonnet |
| H8 | `scripts/check/no_direct_rt_allowlist.txt` | none | Decide per file whether each is a provider or a consumer: `io_runtime.spl`, `io/http_sffi.spl`, `app/io/*_sffi.spl`, `app/io/*_ops.spl`, `nogc_async_mut/io/mod_stub.spl`. Record each decision with a `# reason:`. | Allowlist diff plus the census recount | sonnet |
| H9 | `src/os/kernel/abi/syscall_shim_positioned.spl`, `src/os/sosix/{share,fd_ownership,queue_notify}.spl` | none | Kernel-side health: fix the `sosix_fs_kernel_uninstalled_positioned_state_v1` import drift, and file the seed bug for module-level `[T; N]` globals | `syscall_sosix_share_spec` executes examples again. A bug record is filed. | sonnet |

Every lane runs `bin/simple test --no-session-daemon <spec>` one path at a time. Every lane
brackets its evidence with the binary's identity: `readlink -f bin/simple` and `stat`. Only H4
edits `host_facade.spl`, only H3 edits `time.spl`, and only H5 edits `__init__.spl`.

## 6. Still blocked (unchanged from 2026-09-05)

The blocked rows are C1/C2 (deploy only), C3, C4, C5, F1, G3, G4, AC-3b, and A5. Their owners
and resume commands are in `doc/08_tracking/todo/sosix_unification_blocked_rows_2026-09-05.md`.

The C2 row, `posix_spec`, stays red on the deployed seed until a compiler built after PR #388
is deployed. No lane here may redeploy `bin/release` (state.md, 2026-09-06 10:02).
