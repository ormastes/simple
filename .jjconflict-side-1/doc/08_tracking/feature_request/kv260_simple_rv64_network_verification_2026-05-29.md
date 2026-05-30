# KV260 Simple RV64 Network Verification Feature Request

## Open Requests

### FR-KV260-NET-0001 — Verify SimpleOS RV64 web and SSH on KV260 FPGA

- **Filed-on:** 2026-05-29
- **Filed-by:** Codex KV260 verification follow-up
- **Target:** kv260-simple-rv64-network
- **Priority:** P0
- **Status:** Open
- **Requested-semantics:**
  Add a real network-dependent verification lane for the KV260 Simple RV64
  FPGA target. The lane must distinguish physical FPGA proof from QEMU proof:
  it should load the current Simple RV64 bitstream, capture PL UART through the
  PMOD UART path, verify that the target has a usable network device or bridge,
  and then prove both HTTP and sshd behavior from the host.
- **Acceptance-criteria:**
  - [ ] Physical KV260 run loads `build/build/xilinx_kv260/gateware/xilinx_kv260.bit`
        and records `End of startup status: HIGH`.
  - [ ] Physical PL UART capture records SimpleOS RV64 boot markers from the
        softcore, not only the ZynqMP PS UART sanity marker.
  - [ ] A documented physical network path exists for the Simple RV64 softcore:
        Ethernet MAC, PS/PL bridge, TAP bridge, UART/SLIP bridge, or another
        explicit transport with a stable IP/port mapping.
  - [ ] Physical target log records network initialization reaching a ready
        state equivalent to QEMU `Network service ready`.
  - [ ] Host HTTP probe gets `200` from `/health` and `/` on the physical
        target, and artifacts include request/response logs.
  - [ ] Host SSH probe reaches the sshd banner, completes a password-authenticated
        login or a documented key-auth flow, and records stdout/stderr plus
        target serial logs.
  - [ ] The verification script exits nonzero when physical network is absent,
        sshd is missing, HTTP is deferred, or only QEMU evidence is available.
  - [ ] Guide docs clearly list QEMU-only, RTL-sim-only, and physical-KV260
        evidence separately.
- **Related-upfront:** `doc/03_plan/agent_tasks/riscv64_fpga_simpleos_launch.md`
- **Related-design-doc:** `doc/07_guide/hardware/kv260_rv64gc_fpga_boot.md`
- **Related-issue:** none
- **Notes:** As of 2026-05-29, verified physical evidence covers JTAG
  programming, merged USB PS UART sanity, and the current bitstream reaching
  `End of startup status: HIGH`. The current PL image routes UART to PMOD
  `H12/E10`, and no physical PL UART boot log has been captured. QEMU RV64 logs
  show SimpleOS boot and HTTP bind/listen behavior when virtio networking is
  available, but that is not physical FPGA proof. Existing SSH evidence is not
  sufficient for RV64/KV260; the observed RV64 SSH parity artifact timed out
  during banner exchange.
