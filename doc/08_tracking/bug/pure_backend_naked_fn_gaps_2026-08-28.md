# Pure backend @naked gaps: alloca suppression + E-NAKED validation seed-only; ~{memory} default delta
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Filed:** 2026-08-28 (HAL impl A Opus verification, D1/D2)
**Status:** FIXED 2026-11-11 (lane compiler6) — D1/D2/R1 verified GREEN 11/11 on the seed unit spec; native objdump dual-run half pending the llvm lane (grant recorded in the 2026-11-11 addendum).

## D1 — latent miscompile: pure backend @naked emits allocas
`E-NAKED-BODY`/`E-NAKED-CLOBBER` validation and alloca suppression exist only in
the Rust seed. The pure-Simple backend only stamps `naked noinline` and turns
`Ret` into `unreachable`; a pure-compiled `@naked` fn with any local still emits
allocas inside a `naked` define — invalid prologue-free code. Current specs
hand-build an empty body and do not cover this.

**Fix:** port the seed's E-NAKED-BODY/E-NAKED-CLOBBER checks and alloca
suppression to the pure backend; add a spec with a local in a @naked fn
(must error, not emit alloca). Record as a dual-run pair until parity.

## D2 — three-way `~{memory}` clobber-default delta
Seed impl A, seed impl B (landed), and the pure backend disagree on whether
`~{memory}` is implied for raw asm without explicit clobbers. Needs one
documented default + dual-run record.

Source: $SCRATCHPAD/hal/VERIFY_impl_A.md (commit 644292b2e6a).

## R1 (batch-1 verify, 2026-08-28): @align power-of-two ambiguity
`@align(2)` emits 2-byte alignment, but riscv `.align 2` means 2^2=4
(readelf Addralign 4 vs 2). Decision needed: make @align p2align-semantics or
require byte counts (`@align(4)`) in twins. Until decided, riscv twins must
write the byte count explicitly. Source: $SCRATCHPAD/hal/VERIFY_batch1.md.


## Fix implemented 2026-11-09 — verification pending (native)
- **D1:** pure backend `translate_naked_body` (`_MirToLlvm/core_codegen.spl`) ports the
  seed's `compile_naked_function`: exactly one raw asm block, no operands/clobbers,
  `Ret(nil)`/`Unreachable` only; else `E-NAKED-BODY` / `E-NAKED-CLOBBER` codegen error
  (fail-closed module). The generic block translator is never run for `@naked`, so no
  local/param allocas. Spec: `test/01_unit/compiler/backend/naked_no_prologue_spec.spl`
  (RED 7/11 before, GREEN 11/11 after).
- **D2 (owner: keep conservative):** a raw asm block with no operands and no explicit
  clobbers gets `~{memory}` (opt out with `options(nomem)`) — pure backend now matches the seed.
- **R1 (owner: honor @align as byte count):** `@align(n)` is emitted as LLVM `align n` bytes,
  never p2align; riscv twins write the byte count (`@align(4)`).

## Verification addendum 2026-11-11 — lane compiler6 (FIXED)

Lane compiler6 re-verified the 2026-11-09 fix on the tracked fresh seed
(`bin/simple.exe`, build 46fe8f6b6def, seed-smoke):

* Unit half — `test/01_unit/compiler/backend/naked_no_prologue_spec.spl`
  re-run today: `outcome=OK, declared>=11, executed=11, passed=11, failed=0`.
  The spec drives the PURE backend (`compiler.backend.MirToLlvm.translate_module`
  under the seed) and pins: E-NAKED-BODY on a @naked fn with a local (no
  alloca emitted), E-NAKED-CLOBBER on clobbered asm blocks, E-NAKED-BODY on
  two asm blocks, `naked noinline` + `unreachable` + no `ret` for the valid
  body, the D2 conservative `~{memory}` default for operand/clobber-free raw
  asm, and R1's byte-count @align on the define line. The pure-backend
  implementation cited by the fix note exists at
  `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl:1146`
  (`translate_naked_body`).
* Native objdump half — `scripts/check/check-naked-no-prologue.shs` could NOT
  run on this host: it fatally requires GNU `as` for its selftest oracle
  (absent on this Windows host) and an llvm-feature simple binary
  (`native-build --backend llvm` reports "not available in this build" on the
  tracked seed; `--backend cranelift` links COFF objects via the wrong clang
  and does not honour the ELF unmangled-@global contract the gate checks).
  This is a host-tooling gap, not a defect in the fix.
* Exact grant for the pending half: on a Linux/x86_64 host with an
  llvm-feature simple binary and binutils —
  `SIMPLE_HAL_SEED=<llvm-feature simple> sh scripts/check/check-naked-no-prologue.shs`
  (plus `--twins` for the full start.S twin sweep).
