# Linux Stage 2 bootstrap reports an AVX-512 owner routing error

Status: open. The focused method rename is committed, but a fresh Stage 2 candidate has not passed admission.

The WSL Ubuntu 22.04 bootstrap at source `12b26fb1306` built a 35,544 KB pure-Simple Stage 2 compiler (1015 compiled, 0 failed). Its positional hello-world frontend smoke exited 134 with `non-SIMD instruction reached AVX-512 instruction owner`. The candidate was rejected; no Stage 2 receipt or later stage was admitted. Evidence is preserved under `build/bootstrap/windows-linux-20260927/linux/` in `/home/ormastes/simple-multihost-bootstrap-main`.

## Root cause

GDB and disassembly of that rejected binary show that `backend_requested_target_triple` calls `Avx512InstructionLowerer.lower` at address `0xd6ee0a` immediately after `rt_string_trim`, where its Simple source calls text `.lower()`. The wrong method receives a text value and reaches the AVX-512 catch-all panic. The failure is a native method-name dispatch collision, not an actual scalar MIR instruction selected for AVX-512.

The focused workaround renames the class method to `lower_avx512_inst` and updates its only call site. The unit spec also checks text `.lower()` while importing the AVX-512 owner. The underlying native method binding defect remains a separate compiler issue.

## Verification limit

At main `e4243e67153`, a new WSL Stage 2 run stopped before candidate linking: the Rust seed could not infer the type of `state.entries` in the newly added `src/lib/nogc_sync_mut/sffi/dynlib_lifetime_owner_v1.spl`. Explicit generic arguments did not resolve it. A typed callback experiment then failed during parser discovery. Those SFFI experiments are excluded from the focused AVX-512 branch. The three-cycle session retry cap was reached. The AVX rename has not yet passed the positional hello-world smoke on an exact new Stage 2 candidate.

Next: repair the SFFI bootstrap prerequisite in a separate scoped change, then rerun Stage 2 admission on the focused AVX branch. Confirm the generated call from text `.lower()` no longer targets the AVX-512 method, run the positional hello-world smoke, and require the Stage 2 compiler test matrix before later stages.

Related: [AVX-512 native remaining limits](avx512_native_remaining_limits_2026-09-10.md).
