# Multihost bootstrap resume plan

Status: blocked on host prerequisites; no Stage 2, Stage 3, Stage 4, essential-tool, or release PASS is claimed. Source observed: main `edfa0daab038472319196313594265412f2b2f07` (2026-09-27). Re-pin all three rows to the same current main revision before resuming. Merge owner and final reviewer: Codex.

| Row | Observed result | Required prerequisite | Retained evidence |
| --- | --- | --- | --- |
| Windows MSVC | Stage 2 startup aborted: LLVM 23.1.1 not detected. Requested 20 jobs, memory policy selected 7 of 24 CPUs. | Bind the installed `C:/dev/tool/clang+llvm-23.1.1-x86_64-pc-windows-msvc` provider with `LLVM_SYS_231_PREFIX=/c/dev/tool/clang+llvm-23.1.1-x86_64-pc-windows-msvc`; verify full Stage 2 through Stage 4. | `build/bootstrap/multihost_windows/console.log`; materializer receipt under `build/bootstrap/materialized-links/`. |
| WSL Linux | Default backend lacked LLVM 23. Cranelift fingerprint rejected the distro `llvm-config` symlink; binding its physical path reached Rust seed build, which failed because Cargo 1.75 cannot read lockfile v4. Requested 12 jobs, memory policy selected 9 of 14 CPUs. | Install an admitted native Linux Rust toolchain capable of v4 locks. Select a physical `LLVM_CONFIG` path for Cranelift, or fix the disabled-LLVM fingerprint defect. | `/home/ormastes/simple-multihost-bootstrap-main/build/bootstrap/multihost_linux/console.log` and `logs/x86_64-unknown-linux-gnu/rust-seed-build.log`. |
| FreeBSD QEMU | `--preflight` failed at `admitted_media` before VM startup. | Supply a trusted FreeBSD 14.4 amd64 BASIC-CLOUDINIT qcow2 and SHA-256 through `scripts/qemu/simple-freebsd-media.shs --supply`; permit a safe guest bootstrap jobs setting above the current hardcoded 2. | WSL checker output: 19 preflight checks; reason `admitted_media`. Expected path `/home/ormastes/.simple/qemu/images/freebsd/FreeBSD-14.4-RELEASE-amd64-BASIC-CLOUDINIT-ufs.qcow2`. |

## Resume commands

All commands run from an isolated checkout of the same current `main` revision. Preserve phase-bound caches; do not use Rust seed binaries as Stage 4 evidence.

Windows Git Bash/MSYS2, after binding LLVM 23 and checking its `llvm-config --version`:
```sh
LLVM_SYS_231_PREFIX=/c/dev/tool/clang+llvm-23.1.1-x86_64-pc-windows-msvc SIMPLE_NO_STUB_FALLBACK=1 sh scripts/bootstrap/bootstrap-windows.sh --full-bootstrap --stop-after-stage2 --mode=dynload --jobs=20 --output=build/bootstrap/multihost_windows --no-mcp --produce-stage3-receipt=seed-missing
```

WSL Linux, after installing a lockfile-v4-capable native Rust toolchain:
```sh
LLVM_CONFIG=/usr/lib/llvm-14/bin/llvm-config SIMPLE_NO_STUB_FALLBACK=1 sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2 --backend=cranelift --mode=dynload --jobs=12 --output=build/bootstrap/multihost_linux --no-mcp --produce-stage3-receipt=seed-missing
```

FreeBSD, after media admission and guest job policy review:
```sh
QEMU_MEM=16G QEMU_CPUS=12 sh scripts/check/check-freebsd-bootstrap-qemu.shs --smoke
QEMU_MEM=16G QEMU_CPUS=12 sh scripts/check/check-freebsd-bootstrap-qemu.shs --full
```

After Stage 2 admission, use the emitted exact `--resume-stage3-from-admitted` and `--resume-stage4-from-admitted` commands. Run `scripts/check/check-bootstrap-essential-tools-smoke.shs` against each fresh Stage 4 binary and the canonical platform handoff checker. Compare any source fix with `origin/release/1.0`; backport only affected fixes with separate release-line verification. The previous three Linux attempts reached the session's retry cap.
