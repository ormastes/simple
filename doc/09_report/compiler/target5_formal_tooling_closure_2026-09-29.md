# Target 5 formal tooling closure (2026-09-29)

`src/compiler/70.backend/mir_test_builder.spl` had no live source importer.
The exported and tested builder is
`src/compiler/70.backend/backend/mir_test_builder_full.spl`, so the unused
builder and its closure exception were removed.

The RVFI formal receipt module is consumed by verification tooling and tests,
not by backend code generation. It moved unchanged from
`src/compiler/70.backend/backend/riscv_scalar_rvfi_formal.spl` to
`src/compiler/90.tools/verify/riscv_scalar_rvfi_formal.spl`. Its production
consumer and four specs now import `compiler.verify.riscv_scalar_rvfi_formal`.

The widened kernel closure audit changed from 3 K0-to-P, 9 K1-to-P, and 9
kernel-to-app/OS edges to 3, 7, and 9, with zero unclassified or unresolved
imports. The audit still fails. All seven remaining K1-to-P edges come from
the two compiler-side `_VhdlProcess` files. Their plugin copies exist, but
`vhdl_backend.spl` still reaches the compiler copies. Removing them requires
moving that live backend entry path to plugin dispatch. No native size or
startup result is implied by this source-only cleanup.
