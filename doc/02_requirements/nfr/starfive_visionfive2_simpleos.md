<!-- codex-research -->
# StarFive VisionFive 2 SimpleOS non-functional requirements

Selection: bring-up safety and reproducibility targets, approved by the user on 2026-08-15.

- **NFR-001 — Safety:** normal build/load must never write QSPI or invoke firmware recovery; JTAG reset/halt/write requires explicit action after a valid JH7110 TAP identity.
- **NFR-002 — Identity:** require Tigard FT2232 `0403:6010`, the selected serial, channel A for UART, channel B for JTAG, and expected JH7110 TAP ID `0x07110cfd`.
- **NFR-003 — Reproducibility:** receipt fields and SHA-256 image hash must make a build independently identifiable.
- **NFR-004 — Startup:** first kernel UART marker within one second of U-Boot `bootelf` transfer and shell prompt within ten seconds on a correctly configured board.
- **NFR-005 — CLI latency:** `ls /` completes within 250 ms and reports at least the three deterministic root entries.
- **NFR-006 — Bounded operations:** UART capture and JTAG operations require explicit timeouts; no unbounded polling or retry loop is permitted.
- **NFR-007 — Compatibility:** existing QEMU RV64 and FPGA target catalog rows and console behavior remain unchanged.
- **NFR-008 — Evidence:** software checks and hardware transcripts distinguish PASS, FAIL, and BLOCKED; absence of hardware output is never reported as PASS.
