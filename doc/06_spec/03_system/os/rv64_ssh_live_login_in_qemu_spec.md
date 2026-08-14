# RV64 Live SSH Login in QEMU Specification

> Modern operator manual for the fail-closed RV64 Sv39/PID1/network/SSH/WM gate. Static source contracts do not admit the live row; only retained, ordered runtime evidence may produce `TEST PASSED`.

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
| 7 | 6 | 0 | 1 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Live SSH Login in QEMU Specification

This modern SSpec keeps static configuration regressions separate from the live
admission claim. The live scenario stays red unless an admitted Stage 4 CLI
builds the image and QEMU produces the complete ordered lifecycle transcript.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #simpleos-rv64-ssh-live #simpleos-ssh-live |
| Category | System |
| Status | Static contract implemented; live lifecycle gate blocked by TODO806 |
| Requirements | AC-3, AC-4, AC-5, AC-6, AC-7 |
| Plan | doc/03_plan/sys_test/rv64_ssh_live_login_in_qemu.md |
| Design | `doc/05_design/rv64_sv39_pid1_network_ssh_wm_boot.md` |
| Research | doc/08_tracking/feature/kv260_simple_rv64_network_verification_2026-05-29.md |
| Source | `test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl` |
| Updated | 2026-08-14 |
| Generator | Pending admitted-CLI regeneration and seven-dimension review (TODO807) |

## Overview

The dedicated QEMU lane forwards host port 2222 to guest port 2222. The live
row is deliberately fail-closed: an unset opt-in is a blocker, not a passing
skip. The source lanes are integrated. TODO806 owns admitted combined execution;
TODO808 and TODO809 own focused SSH/WM evidence; TODO807 owns regeneration and
the seven-dimension SSpec-maintain review once the admitted Stage 4 CLI exists.

## Terra Diagnostic Boundary (2026-08-14)

Terminal-only focused checks reported `Checking...`/exit 0 for
`release/x86_64-unknown-linux-gnu/simple check examples/09_embedded/simple_os/arch/riscv64/ssh_live_entry.spl`
and `release/x86_64-unknown-linux-gnu/simple check test/01_unit/os/rv64_wm_boot_resources_spec.spl`.
The matching WM-resource interpreter invocation exited 0 with empty output.
The IPC handoff focused run was also reported PASS. No canonical current-wave
test-artifact files were retained for those observations, so they are useful
diagnostics only and cannot admit TODO806, TODO808, or TODO809.

Conversely, `release/x86_64-unknown-linux-gnu/simple check
test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl` printed `Checking...`
then segfaulted during checker load; no core or log was retained. It proves no
scenario or manual result. The hash-bound compiler probes remain blocked:
the three-probe receipt is `FAIL-FAIL-FAIL` and the newer five-probe baseline
expansion is all build-SIGSEGV/139. Rerun the focused SSpec, maintain scan, and
docgen only after TODO667 provides the admitted Stage 4; retain output and
provenance before calling this mirror generated or reviewed.

## Integrated source boundary

The current source wave adds syscall-18 owned port destruction, unique named
VFS discovery, copied service request/reply framing, public binary FS methods,
VFS-manager mutation routing, POSIX FD VFS READ/WRITE/SEEK/close behavior, and
byte-zero WM/Window framing. SSH remains backed by real filesystem execution
and attempt-local bounded stdout/status capture. These are source contracts,
not a claim that the checker or guest ran. After TODO667, retain the exact
focused destroy, IPC, VFS, FD, SSH, WM, and system-spec logs under
`build/os/rv64-ssh-live/focused/` before either this manual or the live row is
called verified.

P1c makes the ABI and retirement rules explicit: only
`IPC_COPIED_SERVICE_TAG` selects copied service traffic, so legacy zero-length
sends remain legacy; syscall 18 accepts destruction only by the recorded port
owner; and VFS records terminal closes with a monotonic issued-handle watermark
rather than an unbounded retired-handle list. A received close result retires
the final FD, while a lost transport reply leaves it retryable. SOSIX I/O now
uses the same named copied VFS request owner and READ/WRITE/SEEK formats as the
kernel FD path. These contracts require the post-TODO667 focused IPC handoff,
destroy-port, VFS wire, `fd_io_route`, and `sosix/io` rows before any live
lifecycle conclusion; TODO806 remains the sole combined runtime gate.

## Acceptance Criteria

- The `rv64-ssh` scenario resolves and keeps host-forwarded SSH on port 2222.
- The RV64 SSH target uses `examples/09_embedded/simple_os/arch/riscv64/ssh_live_entry.spl`.
- The RV64 entry initializes the RV64 VirtIO network runtime through std facade
  helpers and starts production `SshDaemon` on port 2222.
- The retained serial transcript proves Sv39, PID1, TX, RX, network readiness,
  SSH accept readiness, and process-owned WM frame readiness exactly once and
  in canonical order.
- When `SIMPLEOS_RV64_SSH_LIVE=1` is set, independent OpenSSH connections
  authenticate as `root` with password `simpleos`, execute `true`,
  `simple --version`, and `simple.smf --version`, reject a wrong password, then
  prove a later good connection and the daemon's accept-resumed receipts before
  the host contract prints `TEST PASSED`.

## Operator Steps

1. `Build admitted RV64 boot image` — record Stage 4, provenance, image, and build-log hashes.
2. `Boot QEMU and capture ordered lifecycle receipts` — retain the complete serial log.
3. `Prove OpenSSH login, exec, rejection, and accept-loop recovery` — use independent connections for each command and negative-auth probe.
4. `Prove process-owned WM readiness` — correlate the live WM PID with the first presented frame.

Any missing, reordered, or duplicate receipt; canned command output; passing
disabled row; or uncorrelated WM marker fails the gate.

## Shared Behavioral Oracle

`src/os/rv64_boot_gate.spl` owns `Rv64BootGateState`,
`rv64_boot_gate_advance`, `rv64_boot_gate_verdict`, the canonical receipt
fixture, and `check_rv64_boot_gate_transcript`. The focused unit spec owns
internal transition coverage, first-error retention, post-terminal rejection,
and unknown-token behavior. This system spec does not duplicate those internals;
it binds canonical serial strings to the public checker and requires:

- canonical receipts: `PASS`;
- missing network TX after Sv39/PID1:
  `INCOMPLETE:missing=network-tx-ready`;
- network TX before PID1:
  `FAIL:reordered:expected=pid1-live:observed=network-tx-ready`;
- duplicate Sv39:
  `FAIL:duplicate-or-replayed:sv39-active`.

The live row separately reads `build/os/rv64-ssh-live.serial.log` and requires
the same checker to return `PASS`; the QEMU runner's boolean is not sufficient.

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
bin/simple spipe-docgen test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl --output doc/06_spec --no-index
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
`true`, `simple --version`, and `simple.smf --version` on independent
connections, reject a wrong password, then accept a later good connection.
Until the serial checker passes and that leg prints `TEST PASSED`, RV64 SSH is
not production-ready.

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
- The shared host probe must see `[sshd] SSH daemon listening on port 2222`.
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
expect(scenario.qemu_extra.contains("user,id=n0,hostfwd=tcp::2222-:2222")).to_equal(true)
expect(scenario.qemu_extra.contains("virtio-net-pci,netdev=n0,disable-modern=on,disable-legacy=off")).to_equal(true)
expect(scenario.description.contains("SSH daemon")).to_equal(true)
```

</details>

#### resolves the RV64 SSH target and QEMU command

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(scenario_exists("rv64-ssh")).to_equal(true)
val resolved = scenario_by_name_direct("rv64-ssh")
expect(resolved.name).to_equal("rv64-ssh")
val target = get_riscv64_ssh_live_target()
expect(target.entry).to_equal("examples/09_embedded/simple_os/arch/riscv64/ssh_live_entry.spl")
expect(target.output).to_equal("build/os/simpleos_riscv64_ssh_live.elf")
val cmd = build_scenario_command(scenario_rv64_ssh(), target.output)
expect(cmd[0]).to_equal("qemu-system-riscv64")
expect(cmd.contains("user,id=n0,hostfwd=tcp::2222-:2222")).to_equal(true)
```

</details>

#### keeps the RV64 SSH entry on the production daemon path behind std RV64 facades

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = rt_file_read_text("examples/09_embedded/simple_os/arch/riscv64/ssh_live_entry.spl")
expect(entry.contains("use os.rv64_probe.{")).to_equal(true)
expect(entry.contains("rv64_network_init")).to_equal(true)
expect(entry.contains("fn spl_start()")).to_equal(true)
expect(entry.contains("rv64_network_init()")).to_equal(true)
expect(entry.contains("SshDaemon.new(2222)")).to_equal(true)
expect(entry.contains("daemon.start()")).to_equal(true)
expect(entry.contains("production-daemon-starting arch=riscv64")).to_equal(true)
expect(entry.contains("extern fn rt_riscv_")).to_equal(true)
expect(entry.contains("extern fn rt_net_")).to_equal(false)
```

</details>

#### routes rv64-ssh through the shared OpenSSH host probe contract

<details>
<summary>Executable SSpec</summary>

Runnable source: compiler-selection and dispatch assertions folded for reproduction.
Reproduction: this block contains the executable scenario's compiler and host-probe contract checks.

```simple
val runner = rt_file_read_text("src/os/_QemuRunner/scenario_exec.spl")
val contract = rt_file_read_text("src/os/ssh_qemu_contract.spl")
val build_runner = rt_file_read_text("src/os/_QemuRunner/os_build_run.spl")
val compiler_selector_start = build_runner.find("fn _find_simple_binary_for_target")
expect(compiler_selector_start).to_be_greater_than(-1)
val compiler_selector = build_runner.slice(compiler_selector_start, build_runner.len())
expect(runner.contains("scenario.name == \"rv64-ssh\"")).to_equal(true)
expect(runner.contains("run_rv64_ssh_probe(cmd_parts, timeout_ms)")).to_equal(true)
expect(compiler_selector.contains("src/compiler_rust/target/")).to_equal(false)
expect(build_runner).to_contain("not stderr.contains(\"bootstrap seed only\")")
expect(contract.contains("pub fn run_rv64_ssh_probe")).to_equal(true)
expect(contract).to_contain("run_ssh_probe(\"rv64\", cmd_parts, timeout_ms)")
expect(contract.contains("extern fn rt_process_run_timeout")).to_equal(true)
```

</details>

#### binds canonical and sabotaged serial receipts to the shared boot-gate checker

- Validate the shared boot-gate transcript oracle
- Expected canonical verdict: `PASS`
- Expected missing, reordered, and duplicate verdicts: fail closed as listed
  in Shared Behavioral Oracle

<details>
<summary>Executable SSpec</summary>

```simple
step("Validate the shared boot-gate transcript oracle")
val initial: Rv64BootGateState = rv64_boot_gate_new()
expect(rv64_boot_gate_verdict(initial)).to_equal("INCOMPLETE:missing=sv39-active")
val canonical = prepare_rv64_boot_gate_fixture()
expect(check_rv64_boot_gate_transcript(canonical)).to_equal("PASS")
val missing = canonical.slice(0, 2)
expect(check_rv64_boot_gate_transcript(missing)).to_equal("INCOMPLETE:missing=network-tx-ready")
val reordered = [canonical[0], canonical[2]]
expect(check_rv64_boot_gate_transcript(reordered)).to_equal("FAIL:reordered:expected=pid1-live:observed=network-tx-ready")
val duplicate = [canonical[0], canonical[0]]
expect(check_rv64_boot_gate_transcript(duplicate)).to_equal("FAIL:duplicate-or-replayed:sv39-active")
```

</details>

#### proves the ordered RV64 lifecycle and remains red when live evidence is unavailable

- Build admitted RV64 boot image
- Boot QEMU and capture ordered lifecycle receipts
- Prove OpenSSH login, exec, rejection, and accept-loop recovery
- Prove process-owned WM readiness
- Expected: `TEST PASSED`; unavailable live evidence remains blocked/red


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build admitted RV64 boot image")
step("Boot QEMU and capture ordered lifecycle receipts")
step("Prove OpenSSH login, exec, rejection, and accept-loop recovery")
step("Prove process-owned WM readiness")
if _rv64_ssh_live_enabled():
    val scenario = scenario_rv64_ssh()
    val target = get_riscv64_ssh_live_target()
    if not build_os(target):
        fail("blocked: admitted RV64 boot image build failed")
        return
    val ok = test_scenario(scenario, 900000u64)
    val serial = rt_file_read_text("build/os/rv64-ssh-live.serial.log")
    val gate_verdict = check_rv64_boot_gate_transcript(serial.split("\n"))
    expect(gate_verdict).to_equal("PASS")
    val run_status = if ok: "TEST PASSED" else: "TEST FAILED"
    expect(run_status).to_equal("TEST PASSED")
else:
    print("BLOCKED: admitted Stage 4 and retained QEMU evidence are required")
    fail("blocked: live evidence unavailable")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 1 |


## Related Documentation

- **Plan:** [doc/03_plan/sys_test/rv64_ssh_live_login_in_qemu.md](doc/03_plan/sys_test/rv64_ssh_live_login_in_qemu.md)
- **Research:** [doc/08_tracking/feature/kv260_simple_rv64_network_verification_2026-05-29.md](doc/08_tracking/feature/kv260_simple_rv64_network_verification_2026-05-29.md)


</details>
