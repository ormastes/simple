# Phase Ladder and Component Builds in CI

Two workflows implement the first slice of
`doc/03_plan/infra/bootstrap/free_github_actions_ci_plan_2026-10-22.md`:

| Workflow | What it does | Triggers |
|---|---|---|
| `phase-ladder.yml` | Climbs every bootstrap lane to phase 4, one phase per rung (darwin-x86_64, the slow Intel macOS runner, climbs in its own chain so it never holds the other lanes back), then publishes what each lane reached as the next numbered RC | push to `release/**` and `release_phase3` (bootstrap-relevant paths), nightly 04:17 KST, manual |
| `component-build.yml` | Builds only the kernels, plugins, providers and SIMD variants a change touches, using an already-proven compiler | push and PR on `main`, `release/**`, `release_phase3`; manual |

## Phase ladder

### Lanes

| Lane | Runner | How it climbs |
|---|---|---|
| linux-x86_64 | `ubuntu-24.04` | native |
| linux-riscv64 | `ubuntu-24.04` | cross-built by the previous rung's linux-x86_64 compiler; sanity under qemu-user |
| darwin-arm64 | `macos-15` | native, 3 threads (7 GB runner) |
| darwin-x86_64 | `macos-15-intel` | native |
| windows-x86_64 | `windows-2025` | native |
| freebsd-x86_64 | `ubuntu-24.04` + FreeBSD VM | native inside `vmactions/freebsd-vm` |
| freebsd-riscv64 | none hosted | local QEMU guest; see below |

### One rung

`scripts/bootstrap/phase-ladder-step.shs <platform> <in-dir> <out-dir> [threads]`:

1. Finds the lane's highest phase in the earlier rungs' handoffs (`<platform>-p<N>/`).
2. Stages it as `build/bootstrap/stage<N>/simple`, so the resolver
   (`resolve-bootstrap-compiler.shs`, `config/bootstrap.sdn` `compiler: auto`) picks it.
   Rung 1 has no handoff, so the resolver takes the newest RC instead; when no RC
   package qualifies, the step builds phase 1 with the Rust seed (the `release.yml` commands).
3. Builds phase N+1 with `build-next-phase-ci.shs` (capped at 4).
4. Requires the new compiler to build and run a hello world. `--version` alone is not enough.
5. Writes `<out-dir>/<platform>-p<N+1>/{simple,PHASE}` as the next rung's input.
6. From phase 3 on (`PHASE_LADDER_ESSENTIALS_FROM`, default 3; earlier phases record `not-built`), builds the **essentials** with the new phase: `simple_cli` (`src/app/cli/main.spl`, must answer `--version`), `simple_test_runner` (`src/app/test_runner_new/main.spl`) and `simple_build_runner` (`src/app/buildrunner/main.spl`), into `<handoff>/essentials/` with one line per binary in `essentials/STATUS` (`ok`, `failed`, or `not-built: <reason>`). A failed essential is recorded and its log kept, but does not stop the compiler climbing. Phase-4 essentials carry forward to later rungs. The RC package ships every `ok` essential in `bin/` and keeps `STATUS` as `bin/ESSENTIALS`; the run summary lists each lane's essentials. The riscv64 cross lane records `not-built` for now (it cross-builds only the compiler).

A lane that fails one rung is retried by the next rung from the same input.
Other lanes keep climbing.

### Publishing moves the default compiler

The `publish` job packages each lane's highest phase with
`scripts/release/package-phase1-spk.shs` and creates the next
`rc-<base>-rc.<N>` prerelease. The next ladder, `release.yml` and
`cross-arch-bootstrap.shs --compiler auto` then start from it. That is how
"each RC moves the default compiler forward". Manual runs can opt out with
`publish: false`.

### Running it

```sh
gh workflow run phase-ladder.yml --ref release/1.0.0                      # all lanes
gh workflow run phase-ladder.yml --ref release/1.0.0 -f lanes=linux-x86_64,linux-riscv64 -f publish=false
```

Rung 1 starts from an RC package for the lane or a local stage binary. With
neither, it builds the Rust seed and phase 1 itself, so a lane with no RC package
still climbs. The rung installs what that needs: clang/lld/llvm on Linux, Homebrew
LLVM on macOS, rustup in the FreeBSD VM. Later rungs never use the seed.

### freebsd-riscv64 (local lane)

No hosted riscv64 FreeBSD runner exists. The lane runs in a local QEMU guest:

1. Cross-build the seed and `libsimple_native_all.a`
   (`cross-arch-bootstrap.shs --target freebsd-riscv64` with `FREEBSD_CROSS_CC`
   and `FREEBSD_SYSROOT`).
2. Build stage 1 in the guest with `--backend cranelift` (no `llc` in the guest).
3. Build stage 2 with stage 1.

The guest has no `git`: FreeBSD 14 has no riscv64 package repository. The SCV
cold-init admission only calls `git rev-parse HEAD` and `git ls-files -t`, so a
local stand-in that answers those two from the file tree is enough for a test
VM. Do not commit it.

## Component builds

Registry: `config/ci/components.sdn`. Each component lists:
- `paths`: prefixes whose change rebuilds it. Include the component's own
  sources and what it imports, so a library edit rebuilds its dependents.
- `build`: one command run with `$SIMPLE_BIN`.
- `cache`: the incremental directory.
- `output`: the artifact.

`scripts/ci/plan-components.shs` maps `git diff --name-only base..head` to
components. An unreachable base selects everything, never nothing.
`--selftest` runs first in CI.

Current components:
- kernels: `kernel-x86_64`, `kernel-aarch64`, `kernel-riscv64`
- plugin: `plugin-backend-wasm`
- provider: `provider-cli-native`
- SIMD: `simd-x86_64-avx512` (`--cpu x86-64-v4`, i.e. AVX-512) and
  `simd-aarch64-cross`

Building an AVX-512 variant does not need an AVX-512 CI host. Running it does:
dispatch to a host that reports `avx512f` in `/proc/cpuinfo`.

To add a component, add one `component <name>:` block. No workflow edit is
needed.

### Cache rules

GitHub cache scope is per branch:
- `main` and each release branch save their own entries.
- PRs restore their base branch's entries and never save.

Keys are `component-<name>-<compiler digest>-<sha>`, with restore by
`component-<name>-<compiler digest>-`. So a new compiler never reuses the
previous compiler's objects, and the next commit on the same compiler restores
the previous incremental state. State is saved only after a successful build.

## Known limits

- Path prefixes over-approximate the import closure: any `src/lib/` edit
  rebuilds every component. The exact closure needs
  `src/app/build/targets/change_classifier.spl`, which needs a released
  full-CLI binary to run.
- Everything stops at stage 2 until the stage-2 `surface_build` SEGV is fixed.
  It reproduces on Linux llvm and cranelift, macOS and Windows; FreeBSD x86_64
  shows it as a bus error.
- The remaining 20-lane allocation, slot mutexes, release-selector config,
  provenance/admission, and the manual-debug transport from the plan are not
  implemented yet.
