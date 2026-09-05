# Cosmos NVMe Media Policy Evidence — 2026-08-20

## Result

The missing scoped evidence lane is implemented. The independent C oracle no
longer aliases production names; the stable header pins 36 exact typed exports;
and 196 frozen vectors bind signed runtime inputs and results into digest
`b6a2f693699eb752`. A development diagnostic observed 259/259 C-oracle LLVM
branches with strict Clang diagnostics.

The production Simple owner now carries 63 named decision markers and no
manual coverage counters. The checker requires compiler-generated mapping and
both edges for all 126 outcomes. It also pins the three unchanged C consumer
closures (11 firmware, 2 dispatch, 16 FTL-media imports) and their 3/2/8 public
exports before requiring a closed ELF32 ARM relocatable link.

## Current status

- Source/export/decision-manifest audit: diagnostic PASS, not retained.
- Independent C oracle and frozen 196-row input-bound ledger: diagnostic PASS,
  not retained.
- C oracle LLVM branch diagnostic: 259/259 observed, not retained.
- ARM C consumer compile, exact typed signatures, and static ABI sets:
  diagnostic PASS, not retained.
- Simple parity, compiler edge mapping, focused Simple unit run, generated
  host/ARM owner objects, and final link receipt: BLOCKED pending an explicitly
  supplied admitted current-tree Stage-4 compiler.

The checker intentionally rejects the local Rust seed and any Stage-2/Stage-3
fallback. This report is hardware-independent policy evidence only and does not
change the existing blocked production-board or whole-NVMe status.

Overall status remains `BLOCKED`: without admitted Stage 4 the checker removes
any prior lane receipt, prints diagnostic-only source/C results, and exits 2.

Run the complete lane with:

```sh
SIMPLE_STAGE4_BIN=/admitted/current-tree/simple \
  sh scripts/check/check-cosmos-nvme-media-policy.shs
```
