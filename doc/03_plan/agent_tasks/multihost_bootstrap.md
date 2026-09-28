# Multihost bootstrap resume plan

Status: open; no Stage 3, Stage 4, essential-tool, or release PASS is claimed. The table and commands immediately below record the 2026-09-27 checkpoint at main `edfa0daab038472319196313594265412f2b2f07`. The 2026-09-28 results are recorded after the table. Merge owner and final reviewer: Codex.

| Row | Observed result | Required prerequisite | Retained evidence |
| --- | --- | --- | --- |
| Windows MSVC | Stage 2 startup aborted: LLVM 23.1.1 not detected. Requested 20 jobs, memory policy selected 7 of 24 CPUs. | Bind the installed `C:/dev/tool/clang+llvm-23.1.1-x86_64-pc-windows-msvc` provider with `LLVM_SYS_231_PREFIX=/c/dev/tool/clang+llvm-23.1.1-x86_64-pc-windows-msvc`; verify full Stage 2 through Stage 4. | `build/bootstrap/multihost_windows/console.log`; materializer receipt under `build/bootstrap/materialized-links/`. |
| WSL Linux | Default backend lacked LLVM 23. Cranelift fingerprint rejected the distro `llvm-config` symlink; binding its physical path reached Rust seed build, which failed because Cargo 1.75 cannot read lockfile v4. Requested 12 jobs, memory policy selected 9 of 14 CPUs. | Install an admitted native Linux Rust toolchain capable of v4 locks. Select a physical `LLVM_CONFIG` path for Cranelift, or fix the disabled-LLVM fingerprint defect. | `/home/ormastes/simple-multihost-bootstrap-main/build/bootstrap/multihost_linux/console.log` and `logs/x86_64-unknown-linux-gnu/rust-seed-build.log`. |
| FreeBSD QEMU | `--preflight` failed at `admitted_media` before VM startup. | Supply a trusted FreeBSD 14.4 amd64 BASIC-CLOUDINIT qcow2 and SHA-256 through `scripts/qemu/simple-freebsd-media.shs --supply`; permit a safe guest bootstrap jobs setting above the current hardcoded 2. | WSL checker output: 19 preflight checks; reason `admitted_media`. Expected path `/home/ormastes/.simple/qemu/images/freebsd/FreeBSD-14.4-RELEASE-amd64-BASIC-CLOUDINIT-ufs.qcow2`. |

## 2026-09-28 Windows and WSL result

Both isolated worktrees started from main `3e9bc64d6bf`. FreeBSD was deferred at the user's request. The tested fix commits differ by host: WSL used `12b26fb1306` for the failed AVX-512 guard experiment; Windows used `4c86ae229a1` for the admitted LLVM linker lookup. The reporting branch omits the ineffective AVX-512 guard, so neither host has full-bootstrap PASS on the exact reporting tree.

| Host | Latest result | Next gate | Retained evidence |
| --- | --- | --- | --- |
| Windows MSVC | LLVM 23 and SDK libraries were bound; a 21 MB Stage 2 compiler linked, passed hello-world frontend smoke and struct receiver proof, and produced `stage3-planner-admission.receipt`. The required Stage 2 compiler test matrix then stopped immediately because delegated rows had MC/DC off without `SIMPLE_MCDC_OFF_WAIVER_REASON`. The script forbids Stage 3 resume until this failure is resolved. | In a fresh scoped session, either run the matrix without delegation (`BOOTSTRAP_STAGE2_TEST_DELEGATE=0`) or supply a justified, nonempty MC/DC-off waiver, then require its PASS before Stage 3. | `D:/dev/simple-windows-bootstrap-20260927/build/bootstrap/windows-linux-20260927/windows/console.log`, `logs/x86_64-pc-windows-msvc/stage2-compiler-tests.log`, `stage2-compiler-tests/x86_64-pc-windows-msvc/rejection.env`. |
| WSL Linux | A native nightly Rust toolchain with `RUSTFLAGS=-C link-arg=-Wl,-z,nopack-relative-relocs` produced a runnable seed and passed preflight. Stage 2 linked a 35 MB pure-Simple compiler, but hello-world frontend smoke exited 134 with `non-SIMD instruction reached AVX-512 instruction owner`. An explicit empty-shape guard did not fix it. | Capture the MIR variant and AVX-512 shape map reaching `isel_avx512_frame_inst`; fix the selector and require Stage 2 sanity PASS before Stage 3. | `/home/ormastes/simple-multihost-bootstrap-main/build/bootstrap/windows-linux-20260927/linux/console.log`, `stage3/x86_64-unknown-linux-gnu/stage2-sanity.env.frontend-failure.log`, `stage2/x86_64-unknown-linux-gnu/simple.rejected`; [bug report](../../08_tracking/bug/bootstrap_stage2_avx512_scalar_route_2026-09-28.md). |

The session retry cap was reached. Keep the phase caches and evidence; start any further verify/fix cycle in a fresh scoped session. The release branch has not been changed.

## Earlier resume commands (2026-09-27)

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
