# RV64 Live SSH Login in QEMU Specification

> This Step Base spec restores the RV64 live SSH gate. Static scenarios prove that `rv64-ssh` is a distinct QEMU lane with host port 2222 forwarded to guest port 22 and a production `SshDaemon` RV64 entry. The opt-in live scenario builds the RV64 SSH kernel, boots QEMU, waits for the daemon listening marker, then drives OpenSSH good-password auth/exec and wrong-password fail-closed checks through the shared host-side SSH contract.

<!-- sdn-diagram:id=rv64_ssh_live_login_in_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_ssh_live_login_in_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_ssh_live_login_in_qemu_spec -> std
rv64_ssh_live_login_in_qemu_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_ssh_live_login_in_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Live SSH Login in QEMU Specification

This Step Base spec restores the RV64 live SSH gate. Static scenarios prove that `rv64-ssh` is a distinct QEMU lane with host port 2222 forwarded to guest port 22 and a production `SshDaemon` RV64 entry. The opt-in live scenario builds the RV64 SSH kernel, boots QEMU, waits for the daemon listening marker, then drives OpenSSH good-password auth/exec and wrong-password fail-closed checks through the shared host-side SSH contract.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #simpleos-rv64-ssh-live #simpleos-ssh-live |
| Category | System |
| Status | Static PASS; live opt-in tracks remaining KEX/X25519 blocker |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/rv64_ssh_live_login_in_qemu.md |
| Design | N/A |
| Research | doc/08_tracking/feature/kv260_simple_rv64_network_verification_2026-05-29.md |
| Source | `test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This Step Base spec restores the RV64 live SSH gate. Static scenarios prove that
`rv64-ssh` is a distinct QEMU lane with host port 2222 forwarded to guest port
22 and a production `SshDaemon` RV64 entry. The opt-in live scenario builds the
RV64 SSH kernel, boots QEMU, waits for the daemon listening marker, then drives
OpenSSH good-password auth/exec and wrong-password fail-closed checks through
the shared host-side SSH contract.

Current live completion remains blocked by RV64 pure Simple X25519/KEX evidence.

## Acceptance Criteria

- The `rv64-ssh` scenario resolves and keeps host-forwarded SSH on port 2222.
- The RV64 SSH target uses `examples/09_embedded/simple_os/arch/riscv64/ssh_live_entry.spl`.
- The RV64 entry initializes the RV64 VirtIO network runtime through std facade
  helpers and starts production `SshDaemon` on port 22.
- When `SIMPLEOS_RV64_SSH_LIVE=1` is set, QEMU emits the SSH listening marker,
  OpenSSH authenticates as `root` with password `simpleos`, `true` exec reaches
  the daemon, wrong-password auth fails closed, and the host contract prints
  `TEST PASSED`.

## Step Base

1. Resolve the `rv64-ssh` scenario from the shared QEMU catalog.
2. Verify the scenario carries QEMU user networking with `hostfwd=tcp::2222-:22`.
3. Resolve the RV64 SSH target and verify it points at the RV64 SSH live entry.
4. Build the expected QEMU command and verify it uses `qemu-system-riscv64`.
5. Verify the RV64 entry starts network through std RV64 facade helpers and then
   starts production `SshDaemon`.
6. Verify the runner dispatches `rv64-ssh` through the shared OpenSSH host probe.
7. In opt-in live mode, build the RV64 SSH guest and require OpenSSH auth/exec
   plus wrong-password fail-closed evidence.
8. Store static and live TUI captures under `doc/06_spec/tui/03_system/os/`.

## Syntax

Run static checks:

```bash
bin/simple test test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl --mode=interpreter --clean --timeout 120 --sequential \
  | tee doc/06_spec/tui/03_system/os/rv64_ssh_live_login_in_qemu_spec.txt
```

Run the opt-in live gate:

```bash
SIMPLE_TEST_TIMEOUT=900 \
SIMPLEOS_RV64_SSH_LIVE=1 \
SIMPLE_OS_BUILD_BACKEND=cranelift \
bin/simple test test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl --mode=interpreter --clean --timeout 900 --sequential \
  | tee doc/06_spec/tui/03_system/os/rv64_ssh_live_login_in_qemu_live.txt
```

Generate the manual:

```bash
bin/simple spipe-docgen test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl --output doc/06_spec
```

## Evidence Model

The static leg is release-useful because it proves the missing RV64 SSH lane is
now represented in source, not only in stale generated matcher artifacts. It
checks the scenario catalog, target resolver, QEMU command construction, RV64
entrypoint source, and host-side OpenSSH probe dispatch. That means future live
work has a concrete executable gate and cannot silently fall back to `x64-ssh`.

The live leg is intentionally opt-in. It is the only leg that can prove the full
SSH requirement: OpenSSH must connect through QEMU user networking, receive the
production daemon banner, complete KEX, authenticate `root/simpleos`, execute
`true`, and reject a wrong password. Until that leg prints `TEST PASSED`, RV64
SSH is not production-ready.

## Current Boundary

The RV64 entry uses std RV64 facade helpers for network startup so new
entrypoint code does not bind `rt_*` directly. The production `SshDaemon`
modules still contain runtime-backed network and crypto externs. Those are
existing daemon internals and remain part of the hardening backlog; they must be
moved behind std/simple library facades before the final objective can be marked
complete.

## Remaining Live Blockers

- Pure Simple RV64 X25519/KEX completion must produce nonzero,
  OpenSSH-compatible shared secret and exchange hash evidence.
- The opt-in `rv64-ssh` live run must build a current-source RV64 SSH kernel.
- The shared host probe must see `[sshd] SSH daemon listening on port 22`.
- The OpenSSH good-password transcript must exit zero and the serial log must
  include `[sshd-session] auth ok user=root method=password`.
- The OpenSSH exec transcript must include `[sshd-session] exec command=true`.
- The wrong-password transcript must fail closed and the serial log must include
  `[sshd-session] auth password fail branch`.

## Regression Risks

- A future scenario rename could accidentally route SSH back through x64-only
  evidence. The static scenario and target assertions catch that.
- A future entrypoint edit could call runtime network helpers directly instead
  of std RV64 facades. The source assertion catches `extern fn rt_`.
- A future runner edit could bypass the OpenSSH host probe and only check QEMU
  boot. The host-probe dispatch assertion catches that.
- A future crypto workaround could mask X25519 failure by skipping auth/exec.
  The opt-in live leg still requires OpenSSH `TEST PASSED`.

## Scenarios

### RV64 production SSHD in QEMU

#### registers the RV64 SSH scenario with host-forwarded SSH

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scenario = scenario_rv64_ssh()
expect(scenario.name).to_equal("rv64-ssh")
expect(scenario.arch).to_equal(Architecture.Riscv64)
expect(scenario.qemu_extra.contains("user,id=n0,hostfwd=tcp::2222-:22")).to_equal(true)
expect(scenario.qemu_extra.contains("virtio-net-device,netdev=n0")).to_equal(true)
expect(scenario.description.contains("SSH daemon")).to_equal(true)
```

</details>

#### resolves the RV64 SSH target and QEMU command

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if val resolved = get_scenario("rv64-ssh"):
    expect(resolved.name).to_equal("rv64-ssh")
else:
    expect("missing").to_equal("rv64-ssh")
val target = get_riscv64_ssh_live_target()
expect(target.entry).to_equal("examples/09_embedded/simple_os/arch/riscv64/ssh_live_entry.spl")
expect(target.output).to_equal("build/os/simpleos_riscv64_ssh_live.elf")
val cmd = build_scenario_command(scenario_rv64_ssh(), target.output)
expect(cmd[0]).to_equal("qemu-system-riscv64")
expect(cmd.contains("user,id=n0,hostfwd=tcp::2222-:22")).to_equal(true)
```

</details>

#### keeps the RV64 SSH entry on the production daemon path behind std RV64 facades

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = rt_file_read_text("examples/09_embedded/simple_os/arch/riscv64/ssh_live_entry.spl")
expect(entry.contains("use os.rv64_probe.{")).to_equal(true)
expect(entry.contains("rv64_network_init")).to_equal(true)
expect(entry.contains("fn spl_start()")).to_equal(true)
expect(entry.contains("rv64_network_init()")).to_equal(true)
expect(entry.contains("SshDaemon.new(22)")).to_equal(true)
expect(entry.contains("daemon.start()")).to_equal(true)
expect(entry.contains("production-daemon-starting arch=riscv64")).to_equal(true)
expect((entry.index_of("extern fn rt_") ?? -1) == -1).to_equal(true)
```

</details>

#### routes rv64-ssh through the shared OpenSSH host probe contract

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runner = rt_file_read_text("src/os/qemu_runner_part5.spl")
val contract = rt_file_read_text("src/os/ssh_qemu_contract.spl")
expect(runner.contains("scenario.name == \"rv64-ssh\"")).to_equal(true)
expect(runner.contains("run_rv64_ssh_probe(cmd_parts, timeout_ms)")).to_equal(true)
expect(contract.contains("pub fn run_rv64_ssh_probe")).to_equal(true)
expect(contract.contains("run_ssh_probe(\"rv64\", cmd_parts, timeout_ms)")).to_equal(true)
expect(contract.contains("extern fn rt_process_run_timeout")).to_equal(true)
expect(contract.contains("SSH daemon listening on port 22")).to_equal(true)
```

</details>

#### boots RV64 QEMU and accepts OpenSSH password auth and exec when explicitly enabled

- print
   - Expected: live_status equals `disabled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _rv64_ssh_live_enabled():
    val scenario = scenario_rv64_ssh()
    val target = get_riscv64_ssh_live_target()
    val build_status = if build_os_with_backend(target, "cranelift"): "built" else: "build failed"
    expect(build_status).to_equal("built")
    val ok = test_scenario(scenario, 900000u64)
    val run_status = if ok: "TEST PASSED" else: "TEST FAILED"
    expect(run_status).to_equal("TEST PASSED")
else:
    print("SKIP: set SIMPLEOS_RV64_SSH_LIVE=1 to run the RV64 live SSH QEMU gate")
    val live_status = if _rv64_ssh_live_enabled(): "enabled" else: "disabled"
    expect(live_status).to_equal("disabled")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/sys_test/rv64_ssh_live_login_in_qemu.md](doc/03_plan/sys_test/rv64_ssh_live_login_in_qemu.md)
- **Research:** [doc/08_tracking/feature/kv260_simple_rv64_network_verification_2026-05-29.md](doc/08_tracking/feature/kv260_simple_rv64_network_verification_2026-05-29.md)


</details>
