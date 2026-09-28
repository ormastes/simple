# `check-bootstrap-portability.shs` red on main: 233 stale assertions (2026-09-28)

**Symptom.** CI step "Validate bootstrap portability contracts" (job
`Native — Linux x86_64`, `.github/workflows/rust-bootstrap-multiplatform.yml`)
fails on every main run, e.g. run 36366107375 at `ba0a3190757`:
`FAIL: portable bootstrap process lock`. Reproduces on a Linux host from a
clean `origin/main` worktree (`fe54a686120`).

**Fixed in this change (2 test drifts, first two assertions):**
1. `test/01_unit/scripts/portable_process_lock_test.shs` forged a live owner's
   `owner_start_hex` and expected the claim to stay held. Since `2eb51991053`
   (2026-08-31) `refine_leader_group_state` deliberately demotes exactly that
   shape (pid==pgid leader with a different start time, every member descending
   from it) to dead where `/proc` is readable. The test now expects reclaim on
   `/proc` hosts and keeps the held/75 expectation elsewhere (macOS).
2. `test/02_integration/bootstrap_stage3_source_snapshot_test.shs` fixture
   lacked `src/plugins` and `src/compositions`, which `41748fa2329`
   (2026-09-23) made mandatory authority roots (`missing authority root`).

**Still red (not fixed here — owner decision).** With `fail()` made non-fatal
(no `set -e`; first-failure order, not deduplicated, later lines may cascade),
the script reports **233** failing assertions on main and **106** with PR
#1882's workflow file substituted. The workflow-shape class traces to
`e274cd33719` ("merge all share-history worktree branches into main"), which
dropped the Linux cranelift/llvm matrix pair, the `Install FreeType (Linux)`
step and many gates the script greps for; #1882 restores part of it.

Buckets of the remaining assertions:
- Workflow shape lost in `e274cd33719` (matrix backend pairs, Stage 2/3
  artifacts, dynload/parity/MCP/SMF gates, failure-log retention, concurrency):
  mostly closed by #1882.
- Windows (MinGW env, Cranelift selection, ARM64 COFF gate, policy toolchain).
- FreeBSD (QEMU KVM/media admission, full execution, Stage 4 dynload path).
- Cortex-M33 / retired LLVM-cross workflow retirement assertions.
- Source assertions outside CI: baremetal text/chr/string ABI in
  `examples/09_embedded/simple_os/arch/*/boot/*.c` and
  `src/os/kernel/arch/riscv64/boot/freestanding_runtime.c`; enum identity,
  MIR canonical constructor, pure runtime enum equality, cross-module
  zero-arg receiver fixture.
- Bootstrap script text: "derives from" backend help, macOS
  timeout/zstd/Homebrew prerequisites, Linux linker dependency, full-resource
  CPU profile, Stage 4 low-memory ownership gate.

Rewriting the contract to the current workflow vs. demoting it is an owner
decision; skipping it is not allowed without approval. Re-run the enumeration
after #1882 lands:

    sed -e '9s/exit 1/: /' -e '2s/set -eu/set -u/' \
      scripts/check/check-bootstrap-portability.shs >/tmp/enum.shs
    sh /tmp/enum.shs 2>&1 | grep '^FAIL'

**Note:** the enumeration must run from inside `scripts/check/` — the script
resolves its root from `$0`, so a copy under `/tmp` checks the wrong tree.

## Update 2026-09-28 — after #1882 (rebased on main with #1909/#1913)

Enumeration run from `scripts/check/` in a worktree at origin/main + #1882:

| workflow file substituted | failing assertions |
|---|---|
| origin/main | 231 |
| #1882 | **106** |
| pre-rewind `e274cd33719^` | 107 (106 plus the concurrency pin #1909 changed) |

The #1882 failure set is **identical** to the one you get with the pre-rewind
workflow, so `e274cd33719^:.github/workflows/rust-bootstrap-multiplatform.yml`
has no further content these checks need. None of the 106 remaining
assertions greps content of `rust-bootstrap-multiplatform.yml`. All of them
need an owner decision:

- `freebsd-build.yml` triggers/wiring (module-init, parse-f64, enum f64 payload
  fixtures; full execution; QEMU KVM): 6
- `windows-build.yml` (MinGW `CC_`/`AR_x86_64_pc_windows_gnu`, MinGW triple): 3
- release surfaces still reference the retired LLVM cross workflow: 1
- baremetal C sources (`examples/09_embedded/simple_os/arch/*/boot/*.c`,
  `src/os/kernel/arch/riscv64/boot/freestanding_runtime.c`): ~44
- hosted RV32/FreeBSD cross toolchain spec text: 15
- pure runtime enum equality, cross-module zero-arg receiver fixture,
  focused interpreter regressions: 11
- bootstrap script text (backend help, macOS prerequisites, CPU/Stage 4
  profiles, etc.): the rest

Several of these files were also rewound by `e274cd33719` (`windows-build.yml`,
`freebsd-build.yml`, `release.yml`, `bootstrap-from-scratch.sh`), but they have
been edited heavily since, so restoring them is outside #1882.
