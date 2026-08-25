# Generic external receipt semantic quarantine

## Status

Open. The must-check registry has 19 external-receipt rows. Four currently
replay gate-specific evidence (`riscv32-riscv64-shared`,
`binary-size-go-parity`, `interpreter-startup-parity`, and
`rust-go-benchmark-parity`); the other 15 authenticate reviewer signatures and
generic PASS labels without independently replaying the claimed semantics.

## Containment

Eleven production rows now fail closed after signature authentication and
before loading generic attachments: the five Caret rows plus
`web-server-request-port`, `web-server-gpu-nginx`, `db-server-request-port`,
`db-server-gpu-sql`, `simpleos-sbc-qemu-ls`, and
`simple-generated-vhdl-linux`. A private `fixture-generic` row preserves common
framework coverage only when `MUST_CHECK_SELFTEST=1` and the validator runs
against an isolated fixture root.

## Remaining work

Each quarantined row needs a versioned, registry-owned semantic checker before
it can admit evidence. Four additional generic rows have existing source-side
checkers that should be wired into receipt admission next:
`windows-hook-installation`, `simpleos-clang-hello`,
`simpleos-simple-toolchain`, and `simpleos-server-executables`. Until then the
trusted-reviewer policy remains empty and the ledger rows remain TODO.
