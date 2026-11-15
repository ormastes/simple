# Baremetal: no freestanding runtime for string literals / interpolation (2026-11-15)

- id: `baremetal_no_freestanding_runtime_2026_11_15`
- severity: P2
- status: open (gap filed only; not implemented)

## Gap

A full hello program (`print "hello {x}"`) built for `x86_64-unknown-none`,
`aarch64-unknown-none` or `riscv64gc-unknown-none-elf` compiles to an object.
The baremetal link then fails on undefined runtime symbols:

- `rt_string_new_literal` (every text literal)
- `rt_interp_cstr` (every interpolated text)

No runtime archive targets freestanding: `src/runtime/` is hosted C (libc,
malloc, stdio), and the SimpleOS kernel runtime is linked only on the
`*-simpleos` routes (`simpleos_native_linkers.spl`). So a baremetal image can
use only extern MMIO helpers and integer code, as
`examples/09_embedded/rv64_os_boot/main.spl` does.

## Needed

A freestanding runtime subset with a bump or static allocator, `rt_string_*`,
`rt_interp_*` and a print path that goes to a board-supplied `putc`. It should be
pure Simple first, per `doc/07_guide/os/hal/pure_simple_hal.md`, built for each
baremetal arch and linked by `baremetal_native_link.spl`.

## Repro

The phase-2 compiler `~/xc/simple-p2` (WSL Ubuntu-24.04) is run as
`native-build hello.spl --target riscv64 --emit-object`, and the result is linked
with `ld.lld -T <script>`. The link reports `undefined symbol: rt_string_new_literal`
and `undefined symbol: rt_interp_cstr`.

Related: `baremetal_link_drops_target_hosted_path_2026_11_15` (link route,
fix-implemented-verification-pending, PR #9521).

## Also missing even for the MMIO-only example

The ld.lld route from #9521 links `rv64_os_boot/main.o` with the default script and still fails on `undefined symbol: rt_mmio_write8`. There is also no `_start` entry (the program exports `__simple_main`). Those come from board shims today, as `scripts/check/check-baremetal-efi-boot.shs` does, so they belong in the same freestanding runtime/crt0.
