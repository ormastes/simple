# Baremetal: no freestanding runtime for string literals / interpolation (2026-11-15)

- id: `baremetal_no_freestanding_runtime_2026_11_15`
- severity: P2
- status: fix-implemented-verification-pending (2026-11-17)

## Fix (2026-11-17)
The pure-Simple runtime is `src/lib/nogc_async_mut_noalloc/baremetal/freestanding/bm_rt.spl`,
which provides `rt_string_*`, `rt_interp_cstr`, `rt_println*`, `rt_panic` and a
bump arena. The per-arch asm (`_start`, stack, putc, byte load/store, halt) is in
`crt0_{x86_64,aarch64,riscv64}.S`. `scripts/check/check-baremetal-efi-boot.shs`
boots `examples/09_embedded/freestanding_hello` with exact transcript checks.
x86_64 boots through OVMF, aarch64 through AAVMF, and riscv64 through an OpenSBI
v1.4 fw_payload; all three PASS under QEMU. Still open: the check does the
link itself; `baremetal_native_link.spl` does not link the runtime automatically
yet. Board runs are not yet evidenced. 32-bit blockers are filed in
`baremetal_{riscv32,i686}_no_firmware_boot_lane_2026-11-17.md` and
`baremetal_arm32_aavmf32_no_esp_boot_2026-11-17.md`.

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
