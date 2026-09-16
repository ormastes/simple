# SimpleOS SSP (Stack-Smashing Protector) Codegen — Feature Lag
## Closed 2026-09-16 — ...99-102), gated by an `ssp` flag resolved from `TargetPreset` (Hosted = on, Baremetal = off

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

## Triage note 2026-09-13 — left OPEN: needs a SimpleOS build/QEMU lane unavailable here
- **measured**: the referenced product paths still exist, so there is no removed-code basis for a stale closure.
- **inferred**: reproduction needs the SimpleOS x86_64 build artifacts / QEMU system-test lane (and for the SSP item, a clang hardening-flag build). This triage host is Windows with no such lane, and `bin/simple test` is broken here regardless.
- **inferred**: no work attempted — the changes would land in `src/compiler/**` or `src/app/compile/**`, and a bootstrap is running concurrently in this workspace.

Date: 2026-06-28

Lane: `.spipe/simpleos-alpine-harden-musl-busybox` (AC-9)

## Summary

SimpleOS / the Simple toolchain has no stack-smashing protector (SSP / stack
canaries). PIE and RELRO+`-z now` are already ON by default for ELF hosts, but
SSP is entirely absent and bare-metal explicitly disables it
(`src/compiler/80.driver/build/baremetal.spl:351` → `-fno-stack-protector`).
Alpine-class hardening requires `-fstack-protector-strong` by default on the
desktop OS, configurable for embedded.

## Two halves

1. **C / runtime files (easy, lands first):** add `-fstack-protector-strong` to
   the clang invocation in `src/app/compile/native.spl` (near the `-fPIE` add at
   ~line 436) and to `native_link_hardening_flags()` (~line 99-102), gated by an
   `ssp` flag resolved from `TargetPreset` (Hosted = on, Baremetal = off).
2. **`.spl` → LLVM IR (the feature lag):** the Simple→LLVM IR generator must
   emit the `sspstrong` function attribute (and a `__stack_chk_guard` /
   `__stack_chk_fail` reference) on emitted functions when the active preset
   enables SSP. No infrastructure for per-function LLVM attribute injection of
   this kind exists today — this is non-trivial backend work.

## Why filed (not implemented this pass)

Per repo rule "if perf or hw access problem happen add to perf bug or feature
lag bug. and fix them," and per Opus review: the LLVM-IR attribute-injection
half is real backend codegen work that should not be rushed inside the libc/
busybox lane. The config/policy toggle (`PlatformLinkDefaults.ssp` +
`resolve_hardening`) and the clang half (1) are tractable and tracked as
AC-8/AC-9 in the lane; AC-8 (config policy) is DONE. This doc captures half (2)
as the explicit deferred feature lag.

## Acceptance for closure

- Desktop-preset native binary links with a stack canary (`__stack_chk_fail`
  present in the symbol table); embedded preset can opt out.
- A spec under `test/03_system/os/qemu/os/harden/pie_ssp_relro_preset_spec.spl`
  asserts canary presence for the desktop preset and absence for an opted-out
  embedded preset.

