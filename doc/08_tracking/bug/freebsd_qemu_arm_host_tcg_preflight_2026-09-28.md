# FreeBSD x86_64 QEMU bootstrap on an ARM host

## Observed failure

On the aarch64 release host, `sh scripts/check/check-freebsd-bootstrap-qemu.shs --preflight` reported `freebsd_qemu_preflight_reason=architecture`. The host has an ARM-native `qemu-system-x86_64` binary whose `-accel help` lists `tcg`, and the admitted FreeBSD 14.4 amd64 image and SSH key are available. A fresh worktree also failed the workspace check because `build/freebsd` did not exist yet.

## Fix

Commit `48d7f560da2892579b6fb3a77b123de4a624804f` admits aarch64/arm64 hosts only when x86 QEMU exposes TCG, selects KVM only on a compatible x86 host, and accepts a writable ancestor for a fresh VM output directory. The preflight SSpec uses an ARM host fixture and checks rejection when TCG is absent.

## Evidence and scope

- Source base: `d86255637d31befe6cee52f6be25f32974d559fb` plus the fix commit above.
- Host preflight: PASS, 19 checks, reason `none`.
- Negative preflight with a mock ARM-host x86 QEMU advertising only KVM: exit 1, reason `architecture`.
- QEMU smoke: PASS under TCG; FreeBSD 14.4-RELEASE SSH, root SSH, clang, and a C compile/run succeeded. Its stdout was captured in the run result; a later full-run cleanup removed the log from `build/freebsd/bootstrap-logs/`.
- First full bootstrap reached Stage 2 and exposed a separate LLVM zstd fingerprint failure, recorded in `freebsd_llvm_zstd_bootstrap_fingerprint_2026-09-28.md`. The second canonical run passed that gate, then the Rust runtime C build failed because the VM sync excluded `tools/counterpart/sdk/c/simple_counterpart_abi.h`. The exact guest build log is retained at `build/freebsd/qemu-run-logs/rust-seed-build-failure.log`, SHA-256 `4c417ab7de83ba8c4e6045d965814072778dec91c4186f6f5c5bc67a6dc9754c`.
- Commit `6771f129572d889422ee38b2b3fbf58fb6172d5b` adds only that header and its parent directories to the VM sync. An rsync dry run listed only the header plus parent directories under `tools/`; shell syntax and the 19-check preflight passed.
- The third and final canonical `--full` run used base `d86255637d31befe6cee52f6be25f32974d559fb` plus commits `48d7f560da2892579b6fb3a77b123de4a624804f`, `8f78397c073ecc1d48af5d1326f9f0f57dac099e`, and `6771f129572d889422ee38b2b3fbf58fb6172d5b`. QEMU selected TCG, booted FreeBSD 14.4, synced the header, passed fingerprinting and the Rust seed build (`101m 34s`), then reached `rust-native-all` compilation. The configured 7,200-second Stage 2 SSH timeout expired while native compilation was still active. The wrapper exited 1 with `Canonical FreeBSD stage2 trust-root bootstrap failed`. No completed Stage 2 or full bootstrap was qualified. The copied native build log ends with a warning and no fatal source diagnostic.
- Final stdout: `build/freebsd/qemu-run-logs/freebsd-qemu-full-final.log`, SHA-256 `cb9df481fcc7bf846481530d76f19f813aa7472e471456a049fb25350b04c21e`; copied guest Rust seed and native build logs: `build/freebsd/bootstrap-logs/x86_64-unknown-freebsd/`, SHA-256 `2ab30ce6fcaab93679aa95fda7f5b3b1f7877d7a648b22eacace8e7ca62f1c30` and `26c0a6e5d93d15ddfcbcb47bfdf69fb125d52a3d2fbd76482d023dd742d6c21a`, respectively. The stopped run overlay remains at `build/freebsd/vm/freebsd-run.overlay.qcow2`. These local build outputs are ignored by Git.
- The SSpec requires a source-matched pure-Simple host runtime with the `test` command before execution. The available Stage 2 compiler-only binary reports `unknown command 'test'`; Linux Stage 4 is not yet qualified. This evidence does not qualify a later release source commit. The three-cycle verification cap is exhausted; no fourth VM run was started.
