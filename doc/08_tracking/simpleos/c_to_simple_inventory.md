# SimpleOS C to Simple Inventory

This inventory tracks the remaining kernel and boot-path C or assembly that is
being migrated into Simple for the multi-arch SimpleOS consolidation.

## Wave 1 scope

Wave 1 covers the SimpleOS kernel image and baremetal boot/runtime path only.
Hosted runtime, libc-adjacent support, and third-party code stay out of scope
for this pass.

Priority port targets:

| Priority | Current source | Status | Target Simple owner |
| --- | --- | --- | --- |
| 1 | `src/runtime/startup/baremetal/runtime_minimal.c` | Shared runtime control flow already ported into `src/os/runtime/baremetal/runtime_minimal.spl`; verify remaining call sites and remove residual fallback use. | `src/os/runtime/baremetal/runtime_minimal.spl` |
| 2 | `examples/09_embedded/simple_os/arch/*/boot/baremetal_stubs.c` | Still present as arch shim glue; split into shared runtime core plus thin arch shims. | shared Simple runtime + per-family shim |
| 3 | `src/os/libc/simpleos_crt0.S` | Replace with `HalCstart` implementation per target. | `src/os/kernel/arch/*/cstart.spl` |
| 4 | `src/os/libc/simpleos_setjmp.S` | Replace with `HalCstart.setjmp/longjmp` implementation per target. | `src/os/kernel/arch/*/cstart.spl` |

### RV32 kernel boot slice

`src/os/kernel/arch/riscv32/boot/baremetal_stubs.c` is reduced to one include
of the shared RISC-V freestanding runtime. The RV32 linker-counter accessor is
now a naked Simple assembly boundary in `smp_provider.spl`; its polling decision
is in `smp_policy.spl`. Optional NVMe firmware selection is a Pure-Simple
composition provider, not a weak C hook. The include wrapper remains in a
separate foreign-runtime denominator because minimal native-build currently
discovers the conventional `boot/baremetal_stubs.c` filename; removing it
without changing that manifest would drop the shared runtime ABI closure.

Exact authored-but-unexecuted coverage scope is recorded in
`test/fixtures/os/kernel/arch/riscv32/rv32_hal_coverage_scope.sdn`. It does not
claim coverage for the retained shared C runtime.

## Residual allow-list

The production gate for owned C is zero residual owned `.c` files in the
SimpleOS kernel image outside the documented allow-list.

Allowed external or transitional paths:

- `src/compiler_rust/vendor/**`
- `src/runtime/vendor/**`
- `src/runtime/miniaudio.h`
- `src/runtime/stb_image.h`
- `src/runtime/stb_truetype.h`
- bootstrap wrappers and seed scripts used outside the kernel image build

Everything else is treated as owned code and must either move into Simple or be
reduced to a thin arch shim with an explicit justification.

## Notes

- `runtime_minimal` remains the first shared port anchor because it removes the
  highest-value shared baremetal runtime logic from C.
- `simpleos_crt0` and `simpleos_setjmp` stay explicitly listed here so the
  `HalCstart` replacement work is auditable.
- The generated owned-code audit is emitted at
  `build/multiarch/owned_c_report.json`.
