# Simpleos X86 64 Network Gate Specification

> Tests covering SimpleOS x86_64 network readiness gate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos X86 64 Network Gate Specification

## Scenarios

### SimpleOS x86_64 network readiness gate

#### keeps the x86_64 baremetal runtime on real virtio packet IO

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the x86_64 baremetal runtime on real virtio packet IO


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps the x86_64 baremetal runtime on real virtio packet IO")
val runtime = rt_file_read_text("examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c")
val owners = rt_file_read_text("examples/09_embedded/simple_os/arch/x86_64/boot/runtime_service_owners.c")

# virtio-net PCI device bring-up (MMIO via port I/O, RX/TX rings)
expect(runtime).to_contain("static int _virtio_net_init(void)")
expect(runtime).to_contain("VIRTIO_STATUS_DRIVER_OK")
expect(runtime).to_contain("VIRTIO_NET_F_MAC")
expect(runtime).to_contain("static int _vnet_send_frame(const void *frame, uint16_t frame_len)")
expect(runtime).to_contain("static int _virtio_net_poll(void)")
expect(runtime).to_contain("static int _vnet_reclaim_tx(void)")
expect(runtime).to_contain("_vnet_send_arp_request")
expect(runtime).to_contain("_vnet_handle_icmp")

# device-level TX/RX probes (x86_64 parity with the riscv freestanding runtime)
expect(owners).to_contain("int64_t rt_net_tx_test(void)")
expect(owners).to_contain("int64_t rt_net_rx_ready(void)")
expect(runtime).to_contain("static void _x86_net_probe_txrx(void)")
expect(runtime).to_contain("_vnet_send_arp_request(_vnet.gateway_ip)")

# boot TCP bind path binds port 22 for sshd
expect(runtime).to_contain("int64_t rt_boot_tcp_bind(int64_t addr)")
expect(runtime).to_contain("rt_net_bind(socket_fd, 22)")
```

</details>

#### arms TX before RX and probes are not just device-present checks

- arms TX before RX and probes are not just device-present checks


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("arms TX before RX and probes are not just device-present checks")
val runtime = rt_file_read_text("examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c")

# tx probe must observe a real TX completion, not just _vnet.initialized
expect(runtime).to_contain("_x86_net_tx_ok = (_vnet.tx_count > tx_before && saw_tx) ? 1 : 0;")
expect(runtime).to_contain("_x86_net_rx_ok = saw_rx ? 1 : 0;")

val probe = runtime.find("static void _x86_net_probe_txrx(void)")
val arp = runtime.find("_vnet_send_arp_request(_vnet.gateway_ip)")
expect(probe).to_be_greater_than(-1)
expect(arp).to_be_greater_than(-1)
```

</details>

#### requires packet TX and RX readiness before reporting network ready

- requires packet TX and RX readiness before reporting network ready


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires packet TX and RX readiness before reporting network ready")
val services = rt_file_read_text("src/os/kernel/boot/x86_64_services.spl")

expect(services).to_contain("extern fn rt_net_tx_test() -> i64")
expect(services).to_contain("extern fn rt_net_rx_ready() -> i64")
expect(services).to_contain("val device_id = rt_pci_get_field(i, 6)")
expect(services).to_contain("device_id == 0x1000 or device_id == 0x1041")
expect(services).to_contain("val tx_rc = rt_net_tx_test()")
expect(services).to_contain("val rx_rc = rt_net_rx_ready()")
expect(services).to_contain("[net-x86] Network packet TX unavailable rc=")
expect(services).to_contain("[net-x86] Network packet TX ready")
expect(services).to_contain("[net-x86] Network packet RX unavailable rc=")
expect(services).to_contain("network_ok = 1")

val tx_probe = services.find("val tx_rc = rt_net_tx_test()")
val rx_probe = services.find("val rx_rc = rt_net_rx_ready()")
val ready_set = services.find("network_ok = 1")
expect(tx_probe).to_be_greater_than(-1)
expect(rx_probe).to_be_greater_than(-1)
expect(rx_probe).to_be_greater_than(tx_probe)
expect(ready_set).to_be_greater_than(rx_probe)
```

</details>

#### makes sshd autostart reusable from the boot/init path, not only the gated entry

- makes sshd autostart reusable from the boot/init path, not only the gated entry


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("makes sshd autostart reusable from the boot/init path, not only the gated entry")
val autostart = rt_file_read_text("src/os/apps/sshd/x86_64_sshd_autostart.spl")

expect(autostart).to_contain("os.kernel.boot.x86_64_services")
expect(autostart).to_contain("os.apps.sshd.sshd")
expect(autostart).to_contain("pub fn x86_64_sshd_autostart_on_boot()")
expect(autostart).to_contain("val net_ok = init_x86_64_network_service()")
expect(autostart).to_contain("SshDaemon.new(22)")
expect(autostart).to_contain("daemon.start()")
```

</details>

#### routes the gated ssh_live entry through the shared network service init

- routes the gated ssh_live entry through the shared network service init
   - Expected: live.index_of("val net_init = rt_net_init()") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("routes the gated ssh_live entry through the shared network service init")
val live = rt_file_read_text("examples/09_embedded/simple_os/arch/x86_64/ssh_live_entry.spl")

expect(live).to_contain("os.kernel.boot.x86_64_services")
expect(live).to_contain("val net_ok = init_x86_64_network_service()")
expect(live).to_contain("SshDaemon.new(22)")
# the ad-hoc single-call init must be gone (readiness now goes through the service)
expect(live.index_of("val net_init = rt_net_init()")).to_equal(-1)
```

</details>

#### keeps a virtio-net device attached in the x86_64 q35 QEMU lanes

- keeps a virtio-net device attached in the x86_64 q35 QEMU lanes


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps a virtio-net device attached in the x86_64 q35 QEMU lanes")
val smoke = rt_file_read_text("scripts/os/run_simpleos_q35_smoke.shs")
val scenarios = rt_file_read_text("src/os/_QemuRunner/scenario_disks.spl")

expect(smoke).to_contain("virtio-net-pci,netdev=net0")
expect(scenarios).to_contain("hostfwd=tcp::2222-:2222")
expect(scenarios).to_contain("virtio-net-pci,netdev=n0,disable-modern=on,disable-legacy=off")
```

</details>

#### runs the live x86_64 SSH network bring-up QEMU gate when explicitly enabled

- runs the live x86_64 SSH network bring-up QEMU gate when explicitly enabled


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs the live x86_64 SSH network bring-up QEMU gate when explicitly enabled")
if x86_64_ssh_qemu_live_enabled():
    val result = rt_process_run_timeout(
        "sh",
        ["scripts/os/run_simpleos_q35_smoke.shs", "--profile=c-boot-bridge", "--timeout=60"],
        180000,
    )
    val output = result[0] + result[1]

    # QEMU must attach the virtio-net device and boot the kernel.
    expect(output).to_contain("virtio-net-pci")
else:
    print "SKIP: set SIMPLEOS_X64_SSH_QEMU=1 to run the live x86_64 SSH network QEMU gate"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos_x86_64_network_gate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS x86_64 network readiness gate.
- SimpleOS x86_64 network readiness gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `68a3b96f6bd439be70a1a172cd4ae049ba6e2a1caf2becd949f732c221552e8b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `68a3b96f6bd439be70a1a172cd4ae049ba6e2a1caf2becd949f732c221552e8b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `68a3b96f6bd439be70a1a172cd4ae049ba6e2a1caf2becd949f732c221552e8b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/os/simpleos_x86_64_network_gate_spec.spl
mirror: doc/06_spec/03_system/os/simpleos_x86_64_network_gate_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/simpleos_x86_64_network_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/simpleos_x86_64_network_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/simpleos_x86_64_network_gate_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/simpleos_x86_64_network_gate_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the x86_64 baremetal runtime on real virtio packet IO' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos_x86_64_network_gate_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'arms TX before RX and probes are not just device-present checks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos_x86_64_network_gate_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires packet TX and RX readiness before reporting network ready' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
