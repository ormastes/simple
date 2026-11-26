# Native AArch64: ordered compares encode the wrong CSET condition

- Found: 2026-11-06, XRay PR5b in-process e2e (`work/xray-aarch64-runtime-20261106`).
- Status: fix-implemented-verification-pending (2026-11-26, `work/fix-aarch64-cset-cond-20261126`).

## Cause

`src/compiler/70.backend/backend/native/isel_aarch64.spl:31-36` numbers the
CSET conditions EQ 0, NE 1, LT 2, LE 3, GT 4, GE 5, but
`encode_aarch64.spl:44-58` (`invert_cond`) expects the A64 condition field
(EQ 0, NE 1, GE 10, LT 11, GT 12, LE 13). LT=2 falls to `cond ^ 1` = 3, so
`x < 0` is emitted as `cset hs` (unsigned >=), and LE/GT/GE are wrong the
same way. Only `==` / `!=` are correct.

## Repro

`fn scaled(x: i64) -> i64: if x < 0: return 0 - x / x * 3` built with
`--native --backend=native` (shared) returns `scaled(9) = -9` (expected 27);
disassembly: `cmp x19, x21; cset x20, hs; cbnz x20, <neg path>`.

## Fix direction

Make isel use the encoder's A64 condition values (one shared table). This
changes every native aarch64 object containing an ordered compare, so the
XRay off-identity baseline must be regenerated in the same change.

## Resolution (2026-11-26)

- **Single source of truth**: Defined architectural 4-bit A64 condition codes
  `A64_COND_EQ (0)`, `A64_COND_NE (1)`, `A64_COND_HS (2)`, `A64_COND_LO (3)`,
  `A64_COND_HI (8)`, `A64_COND_LS (9)`, `A64_COND_GE (10)`, `A64_COND_LT (11)`,
  `A64_COND_GT (12)`, `A64_COND_LE (13)` in
  `src/compiler/70.backend/backend/native/mach_inst.spl`.
- **Encoder**: `src/compiler/70.backend/backend/native/encode_aarch64.spl` now
  aliases `COND_*` directly to `A64_COND_*` (re-exported via `__init__.spl`) and
  explicitly handles `COND_HS/LO/HI/LS` alongside `COND_EQ/NE/LT/GE/GT/LE` in
  `invert_cond`.
- **ISel**: Removed the mismatched local `COND_*` table (0..5) in
  `src/compiler/70.backend/backend/native/isel_aarch64.spl`, populated
  `ISelContext.unsigned_locals` from `func.locals` (matching `isel_x86_64.spl`),
  and selected `A64_COND_LT/LE/GT/GE` for signed comparisons and
  `A64_COND_LO/LS/HI/HS` for unsigned comparisons (`U8`/`U16`/`U32`/`U64`).
- **XRay off-identity baselines**: Inspected `xray_sled_emit_aarch64_spec.spl`,
  `emission_order_determinism_spec.spl`, `scripts/check/check-xray-static-off-identity.shs`,
  and `test/fixtures/xray/xray_native_off_identity_driver.spl`. No checked-in
  AArch64 XRay baseline blobs exist in the repository (`check-xray-static-off-identity.shs`
  compares dynamically against a caller-supplied pre-change baseline tree/binary);
  neither unit spec emits `A64_OP_CSET`, so no baseline file updates were required.
- **Verification**:
  - Regression spec extended in `test/01_unit/compiler/backend/native/isel_aarch64_spec.spl`
    (signed `i64` + unsigned `u64`/`u32` + `x < 0` repro asserting `A64_COND_*`
    and exact encoded `CSINC` words).
  - Direct repo invocation via host Nov-15 Rust seed (`/Users/ormastes/simple/bin/simple`)
    cannot load `src/lib/common/types.spl:23` (`unit ByteSize: i64`, added Nov-16).
  - Executed unmodified worktree `mach_inst.spl` / `isel_aarch64.spl` / `encode_aarch64.spl`
    via isolated `/tmp` runner (omitting `types.spl` and stripping `@representation_boundary`
    on temp supporting MIR/HIR copies): RED `SUMMARY fails=8` (all 8 ordered signed/unsigned
    compares wrong, `i64_lt` encoded `0x9A9F37E0` = `cset x0, hs`) -> GREEN `SUMMARY fails=0`
    (12/12 PASS); `isel_aarch64_spec.spl` 10/10 PASS, `xray_sled_emit_aarch64_spec.spl` 6/6 PASS,
    `emission_order_determinism_spec.spl` 2/2 PASS.
  - Full `isel_module_aarch64 -> regalloc_module_aarch64 -> encode_module_aarch64` output
    assembled with `clang -target aarch64-apple-darwin`, disassembled (`objdump -d` confirms
    `cset x20, lt` for `scaled` and `eq/ne/lt/le/gt/ge/lo/ls/hi/hs`), and executed natively
    on Apple Silicon ARM64: `ARM64_HW_VERIFY fails=0 scaled(9)=27 scaled(0)=0 scaled(-9)=9`.
