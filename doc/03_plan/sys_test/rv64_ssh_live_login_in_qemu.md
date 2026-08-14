# RV64 SSH Live Login in QEMU System Test Plan

## Goal

Prove the `rv64-ssh` QEMU lane boots the RV64 SimpleOS SSH image, accepts OpenSSH password login through host port `2222`, executes commands, and rejects bad credentials without regressing the static scenario contract.

## Scope

- Static SSpec coverage for the `rv64-ssh` scenario, QEMU host-forwarding, RV64 entrypoint, OpenSSH host probe dispatch, AES-256-GCM packet fixture, and freestanding child-build compiler selection.
- Opt-in live coverage behind `SIMPLEOS_RV64_SSH_LIVE=1`.
- Evidence artifacts under `build/os/rv64-ssh-live.*` and mirrored manual output under `doc/06_spec/`.

## Acceptance

- [ ] Static run: `SIMPLE_LIB=src SIMPLE_BIN=bin/simple bin/simple test test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl --mode=interpreter --clean --timeout 120 --sequential` passes `6/6`.
- [ ] Build run: `SIMPLE_BIN=bin/simple SIMPLE_OS_BUILD_BACKEND=cranelift SIMPLE_LIB=src bin/simple os build --scenario=rv64-ssh` uses the self-hosted compiler for the child native-build and produces `build/os/simpleos_riscv64_ssh_live.elf` from current source.
- [ ] Sv39/PID1 boot gate: the live image reaches the canonical RV64 boot handoff, activates Sv39, starts PID 1, and retains PID 1 while services run; serial evidence must identify each transition rather than infer it from later output.
- [ ] Network gate: VirtIO network initialization, TX, RX, and the service-ready transition all pass before SSH or WM readiness is emitted.
- [ ] Live SSH gate: with `SIMPLEOS_RV64_SSH_LIVE=1`, the host probe reaches `TEST PASSED`, OpenSSH good auth exits zero, `simple` and `simple.smf` command probes complete, and bad auth fails closed.
- [ ] WM boot gate: the RV64 desktop boot reaches a process-owned WM-ready marker after Sv39/PID1 and network readiness, and the QEMU evidence contract rejects reordered or missing prerequisites.
- [ ] Generated manual: `bin/simple spipe-docgen test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl --output doc/06_spec` reports `0 stubs`.

## Current Blockers

- The current `ssh_live_entry.spl` initializes noalloc services and networking but does not emit or enforce explicit Sv39-active and PID1-live boot receipts.
- The current RV64 desktop-service entry uses a freestanding display scene and a banner-only SSH shim; it does not prove the production daemon and process-owned WM are gated behind the same Sv39/PID1/network lifecycle.
- Live QEMU still needs one fresh bounded run after the seq-4 channel-open fast path and child-build compiler selection fix.
- Completion remains blocked until live evidence proves ordered Sv39/PID1/network readiness, channel-open confirmation, daemon return-to-accept, command execution, SMF launch, bad-auth handling, and WM readiness.
- Restart12 bootstrap evidence (2026-08-14): the checked-in deployed
  pure-Simple CLI crashes in `rt_env_set` before the test runner starts. A
  fresh bootstrap exposed and fixed one multiline-condition parser boundary,
  then exposed an invalid aggregate receiver for
  `CompileContext.error_count()` in Stage 3. Direct scalar ownership reads
  advanced Stage 3 through HIR lowering with zero errors, but the third and
  final bootstrap cycle still segfaulted later in the Stage 3 native build.
  Per the three-cycle cap, no fourth build was attempted. Until a
  provenance-verified Stage 3 compiler exists, the static, build, live SSH,
  and WM criteria remain unverified and this lane is WARN rather than PASS.

## Restart12 Execution Order (2026-08-14)

1. Add a single fail-closed RV64 boot-readiness contract for Sv39, PID1,
   network, SSH, and WM ordering, with focused unit/system coverage.
2. Wire the SSH and desktop entrypoints to the contract without replacing the
   production SSH daemon or process-owned WM with marker-only shims.
3. Run each focused static/build/live criterion once. Use at most three
   verify/fix cycles and retain the first passing evidence.
4. Commit, serialize rebase/push with `/tmp/simple-main-restart12-push.lock`,
   and record the reachable commit only after `origin/main` contains it.
