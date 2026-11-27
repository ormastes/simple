# SimpleOS SSP (Stack-Smashing Protector) Codegen — Feature Lag
## Open — hosted source policy added 2026-09-22; guest evidence pending

The old 2026-09-16 closure heading was a bookkeeping error. The bug database
still marks this item open. Source changes now request Clang
`-fstack-protector-strong` on hosted ELF builds, and emit LLVM `sspstrong` on
hosted SimpleOS functions, excluding bare-metal and naked functions. The
explicit LLVM target API admits hosted `*-simpleos` separately from the kernel
path. The default SimpleOS native-build pipeline still uses Cranelift and maps
its target to `*-unknown-none-elf`; that path needs its own SSP policy before
this bug can close. Guest symbol, startup, and fault-path evidence is also
outstanding.

The LLVM switch now consumes `resolve_hardening(preset).ssp`; its focused spec
proves that `embedded_with_heap` opts out while hosted SimpleOS opts in. An
independent bare-metal guard wins even if a caller supplies a contradictory
hosted or unknown preset. The default Cranelift route remains unresolved
source work.

Source checks on 2026-09-22: focused compiler and app hardening specs passed
(4/4 and 4/4) using the available Rust bootstrap seed. These passes are
diagnostic only; no admitted self-hosted compiler ran them. A Clang
x86_64-unknown-simpleos C probe with a 64-byte local
array and an escaping pointer emitted both `__stack_chk_guard` and
`__stack_chk_fail` undefined references under `-fstack-protector-strong`.
One-shot reciprocal compile measurements: baseline object 1200 bytes, SSP
object 1384 bytes; both 0.01 s; peak Clang RSS 60668 KiB baseline and
61244 KiB SSP. These small fixture measurements are a code-size and build
resource signal, not a guest performance claim.

The focused linkage checker `scripts/check/check-simpleos-ssp-linkage.shs`
also compiles an escaping 64-byte buffer for `x86_64-unknown-simpleos`. The
object has undefined `__stack_chk_guard` and `__stack_chk_fail`; its negative
link without the runtime fails, while the same link with the shipped
`simpleos_cxxabi.c` succeeds and defines both symbols. A host execution of the
shipped failure handler emits `stack smashing detected` and terminates with
status 134. One-shot measurements on 2026-09-22 were 1184 bytes without SSP
and 1848 bytes with the linked handler (+664 bytes), with 0.00 s link time and
25,420/25,224 KiB linker peak RSS respectively. The handler execution used
696 KiB peak RSS. These are focused regression bounds, not guest runtime
performance evidence.

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

## Deferred environment TODO — 2026-09-22

TODO: after the Linux bootstrap publishes an admitted self-hosted compiler,
run the SSP system spec above and `sh scripts/check/check-simpleos-bootstrap-qemu.shs --full`.
Retain the linked kernel symbols, guest failure-handler receipt, and peak RSS;
the focused Clang/source checks do not close this QEMU acceptance row.

## Fix verification
2026-11-12: the focused hosted repro spec
`test/01_unit/compiler/backend/simpleos_ssp_codegen_spec.spl` failed 2/5 under
the Rust seed on release/1.0.0. Both failures were stale assertions against
intentional upstream contracts, not SSP policy regressions: (1) MIR arrays are
boxed references, so `Alloc` of an `Array(U8,64)` local emits an `alloca ptr`
slot, never an inline `alloca [64 x i8]` — the spec now asserts the real slot
while keeping the `sspstrong` / escape-call assertions; (2) the fail-closed
naked contract (E-NAKED-BODY, pure_backend_naked_fn_gaps_2026-08-28, landed
2026-11-09) poisons a non-asm naked body instead of emitting
` naked noinline` IR — the spec now asserts the error module and absence of
`sspstrong`. Spec repaired; verified 5/5 PASS hosted (seed, interpreter mode).
Neighbors green: hardening_preset_policy 12/12, naked_no_prologue 11/11,
aarch64_float_reject 8/8. Still open per above: default Cranelift-route SSP
policy and QEMU guest evidence.

## W2-4 Update (2026-11-27) — `compile_c_to_object` SSP wiring added; compiler Cranelift slice still `open`

- **CLI wrapper fix (`src/app/compile/native.spl`):** Extracted `native_c_object_compile_flags(platform: text, sanitize: bool) -> text` and updated `compile_c_to_object` to apply `native_stack_protector_flags(detect_platform())` (`-fstack-protector-strong` on `"linux"`, `"freebsd"`, `"simpleos"`), matching `compile_native_source`.
- **Host spec:** Extended `test/01_unit/app/compile/native_hardening_spec.spl` with `native_c_object_compile_flags` matrix checks -> `5 total, 5 passed, 0 failed`.
- **Remaining open slice (out of W2-4 scope):** `src/compiler/**` still lacks Cranelift-route SSP policy for baremetal/SimpleOS codegen, and QEMU system verification (`test/03_system/os/qemu/os/harden/pie_ssp_relro_preset_spec.spl`) remains pending. Status kept `open`.

## W4-8 Update (2026-11-27) — `fix-implemented-verification-pending` (preset-gated `native.spl` SSP & source compile contract)

- **CLI native wrapper (`src/app/compile/native.spl`):**
  - Added `native_stack_protector_flags_for_preset(platform, preset)` (`"baremetal"` and `"embedded_with_heap"` opt out cleanly; hosted/default delegates to `native_stack_protector_flags(platform)`).
  - Extracted `native_c_object_compile_flags_for_preset(platform, sanitize, preset)` (kept `native_c_object_compile_flags` delegating with `"hosted"`) and `native_c_source_compile_flags(platform, sanitize, opt_level, use_lto, march_target, preset)` (used directly by `compile_native_source`) so core-C source flags are pure and unit-testable without shelling out.
- **Host unit verification:** Extended `test/01_unit/app/compile/native_hardening_spec.spl` (`7 total, 7 passed, 0 failed`, `--mode=interpreter` on seed). Note: `test/01_unit/compiler/backend/simpleos_ssp_codegen_spec.spl` remains `1 passed, 4 failed` under the Windows seed interpreter (`MirToLlvm.create_explicit_target_with_hardening` returns `nil`; `src/compiler/**` out of W4-8 scope).
- **Status:** `fix-implemented-verification-pending` — `waiting-for:` Cranelift SSP codegen under `src/compiler/**` and QEMU guest execution of `test/03_system/os/qemu/os/harden/pie_ssp_relro_preset_spec.spl`.
