# riscv64 OpenSBI real-firmware gate: 0-byte serial, no banner (2026-08-23)

Status: OPEN. Host: macOS aarch64 (Darwin 25.5.0), qemu-system-riscv64 from Homebrew.

## Command

```sh
sh scripts/check/check-simpleos-riscv64-opensbi-real-firmware-boot.shs
```

## Verdicts

Before the firmware-discovery fix (discovery was Linux-only: `/usr/share/qemu`,
`/usr/share/opensbi`):

```
ERROR — nothing was checked: no OpenSBI fw_dynamic image found (set OPENSBI_FW_DYNAMIC)
```
rc=2.

After adding the macOS Homebrew fallback
`/opt/homebrew/share/qemu/opensbi-riscv64-generic-fw_dynamic.bin` to the
candidate list (repo-pinned `build/os/rv64_soc/.../fw_dynamic.bin` still first):

```
FAIL — no OpenSBI banner found on serial within 12s (log: /Users/ormastes/simple/build/os/rv64_opensbi_realfw_probe/serial.log)
```
rc=1. This is the intended end state of the discovery fix: the gate now reaches
a real measurement with a stated reason instead of erroring out before checking
anything. The FAIL itself is NOT fixed.

## Finding

`build/os/rv64_opensbi_realfw_probe/serial.log` is **0 bytes** after the run —
QEMU emitted nothing at all on the serial device, not a truncated or garbled
banner. Firmware actually used:

```
firmware=/opt/homebrew/share/qemu/opensbi-riscv64-generic-fw_dynamic.bin
sha256=49bdf7b939bda11321132d1042bf99d7324fb190f1feef423171fed3573f8705
argv: qemu-system-riscv64 -machine virt -cpu rv64 -m 256M -display none -no-reboot \
      -bios <fw> -serial file:<log>
```

## Hypothesis — UNVERIFIED

A generic `fw_dynamic` image may require a prior-stage loader to hand it a
`struct fw_dynamic_info` (next-stage address/mode) before it prints its banner;
booted bare via `-bios` with no payload it may fault or spin before any console
output. This has **not** been verified — no instruction trace, no `-d int` run,
no comparison against `fw_jump`/`fw_payload` or against the repo-pinned OpenSBI
v1.4 build has been done. Treat it as a lead, not a cause.

Next steps (none attempted): re-run with `-d unimp,guest_errors -D` or `-d int`;
try the repo-pinned build from `scripts/os/build_opensbi_rv64_soc.shs`; try
`fw_jump.bin` with an explicit `-kernel` payload to isolate whether the silence
is fw_dynamic-specific.
