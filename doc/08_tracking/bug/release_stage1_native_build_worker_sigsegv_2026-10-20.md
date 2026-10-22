# Release stage1 native-build crashes before producing any binary

Canonical ID: `release_stage1_native_build_worker_sigsegv_2026_10_20`

Status: OPEN. A workaround is active in `.github/workflows/release.yml`
(build-bootstrap "Create distribution package", the test-runner block marked
`@workaround bug=release_stage1_native_build_worker_sigsegv_2026_10_20`).
Registered in `doc/08_tracking/bug/bug_db.sdn` (bugs_active + bugs); this dated record is
the authority for diagnosis and acceptance.

## Failure

release.yml `build-bootstrap` builds stage1 (`build/bootstrap/stage1/simple[.exe]`)
from `src/app/cli/bootstrap_main.spl` with the bootstrap-only Rust seed:
`native-build --source src/compositions/kernel_llvm_cranelift --source src
--entry-closure --mode dynload` (plus `SIMPLE_NATIVE_BUILD_RUST=1`). The stage1
`--version` command works. Every `native-build` that stage1 runs then crashes
in the compiler itself, before any binary is written:

- **linux-x86_64**: run 39357315407, job 118415237993, ref `work/rc1-ci-trial`.
  - `src/app/test_runner_new/main.spl`: parse finishes for 285 modules. The
    single worker then dies at `phase=hir` on
    `app.test_runner_new.test_runner_main`:
    ```
    error: native-build worker terminated with signal 11 before producing a binary; NOT a compile failure.
      A SIGSEGV/SIGABRT is a crash in the compiler itself; take a backtrace from the core (see /var/crash).
    ```
  - `src/app/mcp/main.spl` and `src/app/simple_lsp_mcp/main.spl`: HIR shard
    workers report `[hir-shard] owner=0/1@N status=CRASH exit=-139`. The summary
    is `completed_workers=1 failed_workers=25 failed_modules=25`, followed by
    `error: HIR aggregate failure; final worker and artifact publication blocked`.
- **windows-x86_64**: run 39357315407, job 118415238097. This run includes the
  seed fix from PR #3942, which reduced the stage1 link stubs to `stat64i32`,
  `strtok_r` and `swprintf`. All three stage1 native-builds (MCP, LSP-MCP, test
  runner) segfault immediately, with no compiler output:
  `Segmentation fault ... "$BINARY_TO_PACKAGE" native-build ...`.
  The remaining stubs are unconfirmed suspects. For example, `swprintf` is used
  by the Windows process-spawn wrapper path in `src/runtime/runtime_process.c`.

**Update (run 39362039541, job 118430432384).** The Windows segfault was caused
by `MSYSTEM=MINGW64`: the seed picked the GNU flavor and built the core-C
runtime with MinGW headers. release.yml now pins `SIMPLE_LINKER_FLAVOR=msvc`, and
PRs #3942 and #3953 fixed the system-symbol stubs. Stage1 then links with zero
stub warnings and no longer segfaults. Each stage1 native-build now fails
cleanly instead:
`fatal: called unresolved symbol rt_secure_temp_dir_set_parent (stubbed for link only)`.
That runtime symbol has no Windows definition in the stage1 link. The seed
fallback still applies on Windows for this reason. Linux in the same run still
fails with the HIR worker SIGSEGV (job 118430432407).

The Linux MCP builds hit the same crash on earlier runs. They were masked
because those builds are non-fatal ("source fallback remains available").

## Workaround

The test-runner block in release.yml tries stage1 first. When stage1 fails, it
rebuilds `src/app/test_runner_new/main.spl` with the same bootstrap-only Rust
seed and flags that produced stage1. The step prints which producer built the
runner. It records the producer in `bin/simple_test_runner.provenance` inside
the `.spk`, so the rc1 artifact states where the runner came from.

Workaround commit: the release.yml change that introduces the marker on
`work/rc1-release-win-linux` (PR #3930).

## Fix owner / next steps

- Get a backtrace of the Linux HIR worker crash on
  `app.test_runner_new.test_runner_main`. Keep the core, or run the worker
  under gdb with `SIMPLE_NATIVE_BUILD_WORKER=1`.
- Check whether the Windows crash is the same defect or comes from one of the
  three remaining fabricated stubs.
- Once stage1 builds the runner, remove the seed fallback in a separate linked
  change. The provenance file must then say `stage1`.
