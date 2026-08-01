# RV64 SSH Live Login in QEMU System Test Plan

## Goal

Prove the `rv64-ssh` QEMU lane boots the RV64 SimpleOS SSH image, accepts OpenSSH password login through host port `2222`, executes commands, and rejects bad credentials without regressing the static scenario contract.

## Scope

- Static SSpec coverage for the `rv64-ssh` scenario, QEMU host-forwarding, RV64 entrypoint, OpenSSH host probe dispatch, AES-256-GCM packet fixture, and freestanding child-build compiler selection.
- Opt-in live coverage behind `SIMPLEOS_RV64_SSH_LIVE=1`.
- Evidence artifacts under `build/os/rv64-ssh-live.*` and mirrored manual output under `doc/06_spec/`.

## Acceptance

- Static run: `SIMPLE_LIB=src SIMPLE_BIN=bin/simple bin/simple test test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl --mode=interpreter --clean --timeout 120 --sequential` passes `6/6`.
- Build run: `SIMPLE_BIN=bin/simple SIMPLE_OS_BUILD_BACKEND=cranelift SIMPLE_LIB=src bin/simple os build --scenario=rv64-ssh` selects `src/compiler_rust/target/bootstrap/simple` for the child native-build and produces `build/os/simpleos_riscv64_ssh_live.elf`.
- Live run: with `SIMPLEOS_RV64_SSH_LIVE=1`, the host probe reaches `TEST PASSED`, OpenSSH good auth exits zero, `simple` and `simple.smf` command probes complete, and bad auth fails closed.
- Generated manual: `bin/simple spipe-docgen test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl --output doc/06_spec` reports `0 stubs`.

## Current Blockers

- Live QEMU still needs one fresh retry after the seq-4 channel-open fast path and child-build compiler selection fix.
- Completion remains blocked until live host-probe evidence proves channel-open confirmation, daemon return-to-accept, command execution, SMF launch, and bad-auth handling.
