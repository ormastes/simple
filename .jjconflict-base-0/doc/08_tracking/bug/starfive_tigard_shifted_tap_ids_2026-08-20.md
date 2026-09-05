# StarFive Tigard scan intermittently returns shifted TAP IDs

Status: OPEN — physical wiring/signal-integrity action required

On 2026-08-20 the connected Tigard remained stable by USB identity, but fresh
OpenOCD sessions at both 100 kHz and 10 kHz returned IDs such as `0x874bc781`
and `0x3f38807f` instead of the two required `0x07110cfd` TAPs. OpenOCD also
reported IR capture errors and could not examine any U74 hart. No SBI reset,
RAM load, or NVMe write occurred in these failing sessions; UART stayed silent.

The scan wrapper had a false-positive defect: it searched for `0x07110cfd`
anywhere, including OpenOCD's “expected 1 of 1” error text. The wrapper now
requires exactly two actual `tap/device found` records and rejects unexpected-ID
and IR-capture errors. Its synthetic regression self-test proves error text
cannot pass.

Next physical action: with power removed where required by the board procedure,
inspect/reseat VTref, common ground, TCK/TMS/TDI/TDO, and connector orientation.
Then run one read-only scan at a conservative clock. Only after two exact TAPs
pass in the same raw log may software reset or RAM staging resume.

Retained evidence:

- `build/test-artifacts/starfive-jh7110/live-20260820-resume/openocd-sbi-reset-after-clean-scan.log`
- `build/test-artifacts/starfive-jh7110/live-20260820-resume/uart-sbi-reset-after-clean-scan.log`
