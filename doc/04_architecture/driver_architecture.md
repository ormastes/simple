# Driver & Native-Lib Architecture

> Status: Phase A (Foundation) landed. Phases B–E incremental.
> Scope: every OS driver and every native library written in Simple.
> Alignment: **kernel and drivers stay MDSOC-only** (MDSOC+ does not apply here —
> userland services/apps use MDSOC + ECS; see `mdsoc_architecture_tobe.md`).

## 1. Why

Today every Simple driver is statically linked into a monolithic kernel
artifact. There is no runtime driver-loader ABI, no shared manifest, no
dynamic native-library loading. This document defines a single framework
where:

- one `.spl` source yields either a **statically-linked** driver *or* a
  **dynamically-loadable** SMF module — the build profile picks, the source
  is identical;
- drivers are **pure Simple** by default; C drivers are legal only as an
  SFFI shim that implements the same `Driver` trait;
- native libraries (e.g., `lld_ffi`, `cuda_ffi`) share the same loader path
  as drivers — they differ only in whether the `driver_*` entry points are
  required.

## 2. Feasibility Audit — Pure-Simple Drivers

Every capability a driver needs already exists in the Simple toolchain:

| Capability            | Status   | Evidence                                                              |
|-----------------------|----------|-----------------------------------------------------------------------|
| Bitwise `& \| ^ ~ << >>` | works    | `HirBinOp::{BitAnd,BitOr,BitXor,BitNot,Shl,Shr}` in `src/compiler/20.hir/hir_definitions.spl` |
| MMIO read/write       | works    | `src/lib/nogc_sync_mut/io/volatile_ops.spl` — `volatile_read/write_u8/16/32/64`, barriers |
| Inline assembly       | works    | `InlineAsm` HIR + per-arch backends `x86_asm.spl` / `arm_asm.spl` / `riscv_asm.spl` |
| `@interrupt` handlers | works    | `src/compiler/70.backend/interrupt.spl`                                |
| No-GC / no-alloc      | works    | `src/lib/nogc_async_mut_noalloc/`, `src/lib/nogc_sync_mut/`           |
| C ABI export          | works    | `@export("C")` → `c_backend_translate.spl`                             |
| Bitmaps (shift+mask)  | works    | manual; see Phase C for native bitfield sugar                          |
| DMA-coherent alloc    | **gap**  | Phase C introduces `src/lib/nogc_sync_mut/io/dma.spl` (all 6 arches)   |
| Runtime driver loader | **gap**  | Phase B reuses SMF + `99.loader/` + new `.drv_manifest` section        |
| Probe / bind DSL      | **gap**  | Phase B — `@driver(vendor=…, device=[…], class=…)` attr on modules     |
| Cranelift `>>` bug    | **bug**  | known issue (memory `feedback_cranelift_shr_bug.md`); Phase C fix      |

**Conclusion:** nothing blocks pure-Simple drivers at the language level.
Gaps are purely system-level and tracked below.

## 3. Unified Grammar — One Source, Two Link Modes

Every driver and every native lib is a `.spl` module with a manifest
attribute. The syntax is identical for both:

```spl
@driver(class = DriverClass.Block,
        vendor = 0x8086,
        device = [0x2922, 0x2829],
        version = "1.0")
module ahci:

    use std.driver.core.{Driver}
    use std.driver.error.{DriverError}

    struct Ahci:
        # per-driver state (populated in init)

    impl Driver for Ahci:
        fn manifest_abi_rev() -> i32 = 1
        fn init(ctx: DriverContext) -> Result<(), DriverError>: ...
        fn probe(dev: DeviceId) -> Result<ProbeResult, DriverError>: ...
        fn attach(dev: DeviceId) -> Result<DriverHandle, DriverError>: ...
        fn detach(h: DriverHandle) -> Result<(), DriverError>: ...
        fn suspend(h, state) -> Result<(), DriverError>: ...
        fn resume(h) -> Result<(), DriverError>: ...
        fn ioctl(h, cmd) -> Result<i64, DriverError>: ...

    @interrupt fn irq_handler(vec: u8):
        ...
```

Native libs use `@native_lib(abi = "simple", version = "1.0")` and omit the
`Driver` impl:

```spl
@native_lib(abi = "simple", version = "1.0")
module gpu_math:
    @export("C") fn gpu_math_init(): ...
    @export("C") fn gpu_math_dot(a: *f32, b: *f32, n: i64) -> f32: ...
```

The compiler lowers both attributes to the **same manifest section**
(`.drv_manifest`) in SMF. The kernel-side loader reads the section and:

- if `@driver(...)`: invokes `driver_init` then registers the instance in
  the driver table and waits for device matches;
- if `@native_lib(...)`: exposes the module's exports via the existing
  `module_registry` path used by `lld_ffi` and `cuda_ffi` today.

## 4. Static vs Dynamic — One Pipeline

| Axis                | Static mode                                  | Dynamic mode                                         |
|---------------------|----------------------------------------------|------------------------------------------------------|
| Build flag          | `--driver-mode=static`                       | `--driver-mode=dynamic`                              |
| Artifact            | driver `.o` linked into kernel ELF           | standalone `.lsm` SMF library                        |
| Registration        | linker-aggregated `__driver_table` (Linux-style `__initcall`) | `module_loader.spl` reads `.drv_manifest`, calls `driver_init`, inserts into driver table |
| Relocation          | static link time                             | `smf_mmap_native.spl` + `object_resolver.spl`        |
| Unload              | never                                        | dependency-tracked via loader (Phase B)               |
| Source differences  | **none** — same `.spl`                       | **none** — same `.spl`                               |

The `--driver-mode=both` flag emits both artifacts from one compilation
unit (shared IR, split codegen).

## 5. SFFI Bridge for C Drivers

A C driver reaches the kernel only through a Simple shim:

```spl
@driver(class = DriverClass.Block, vendor = 0x1B36, device = [0x000E], version = "1.0")
module legacy_nvme_shim:

    extern fn c_nvme_driver_init(ctx: i64) -> i32
    extern fn c_nvme_driver_attach(bdf: i64) -> i64
    extern fn c_nvme_driver_detach(h: i64) -> i32

    struct LegacyNvme:
        ctx: i64

    impl Driver for LegacyNvme:
        fn manifest_abi_rev() -> i32 = 1

        fn init(ctx: DriverContext) -> Result<(), DriverError>:
            match c_nvme_driver_init(ctx.opaque):
                0 -> Result.Ok(())
                _ -> Result.Err(DriverError.IoError)

        # ... other entry points delegate the same way ...
```

`sffi_lint.spl` (Phase B) enforces:

- every `extern fn` declared in a driver module has a matching wrapper that
  maps C status codes to `DriverError`;
- the module also declares a pure-Simple `impl Driver` — no driver is ever
  “just C”.

## 6. Device-Class Traits Extend the Core Trait

Class-specific traits already in the repo (`FsDriver` in
`src/lib/nogc_sync_mut/fs_driver/ops.spl`, `GpuDriver` under
`src/lib/nogc_sync_mut/gpu_driver/`) compose on top of `Driver`:

```
trait FsDriver:            # fs-specific ops: mount/open/read/...
trait GpuDriver:           # gpu-specific ops: alloc/dispatch/...

struct Fat32: ...
impl Driver  for Fat32: ...     # generic lifecycle
impl FsDriver for Fat32: ...    # fs ops on top
```

No inheritance; the two traits compose (per repo rule). The kernel talks
to each driver through whichever surface matches the operation.

## 7. CPU Architecture Coverage

Supported arches (runtime already present): **x86_64, x86, aarch64, arm32,
riscv64, riscv32.** Per-arch glue lives under `src/hardware/<arch>/` (MMIO
helpers, IRQ controller bindings for IDT/GIC/PLIC, interrupt entry stubs).
The driver framework itself is arch-agnostic. Phase C adds
`src/hardware/<arch>/dma_impl.spl` for all six — cache-line size, coherency
mode (coherent vs non-coherent), and clean/invalidate semantics differ per
arch.

## 8. Security & Isolation

In-kernel drivers (all of today's drivers) run with full kernel privilege —
matches Linux / Zephyr. The framework does **not** yet add per-driver
sandboxing; that is a future MDSOC extension tracked separately. The
manifest's `capability` field (Phase B) allows the kernel to refuse loading
a driver whose declared capabilities exceed policy.

## 9. Phased Rollout

| Phase | Scope                                                                 | Commit |
|-------|-----------------------------------------------------------------------|--------|
| A     | This doc + author guide + `Driver` trait + types + error              | 1      |
| B     | `@driver` / `@native_lib` parsing; `.drv_manifest` SMF section; kernel-side `driver/loader.spl`; `sffi_lint` shim rule; `__driver_table` aggregator | 1 |
| C     | `io/dma.spl` + 6 arch impls; Cranelift `>>` fix; bitfield sugar        | 1      |
| D     | Migrate `fs_driver`, `gpu_driver`, `lld_ffi`, `cuda_ffi`               | 1      |
| E     | Migrate `examples/simple_os/drivers/*` — 1 driver per sub-commit       | N      |

## 10. Comparison with Other OS Driver Models

| OS       | Format       | Load              | Probe/Bind                | Dynamic? |
|----------|--------------|-------------------|---------------------------|----------|
| Linux    | `.ko` (ELF)  | modprobe/insmod   | `MODULE_DEVICE_TABLE`     | yes      |
| Windows  | `.sys` (PE)  | PnP manager       | INF + GUID                | yes      |
| macOS    | `.kext`      | kextload          | IOKit personalities       | yes      |
| UEFI     | `.efi`       | `LoadImage`       | GUID protocols            | yes      |
| Fuchsia  | `.so` + cm   | driver manager    | bind rules DSL            | yes      |
| seL4     | `.a` static  | CapDL init        | manual caps               | no       |
| Zephyr   | `.elf`       | link-time modules | devicetree `CONFIG_*`     | both     |
| **Simple** | `.lsm` (SMF) | `99.loader/` + `driver/loader.spl` | `@driver(vendor,device,class)` attr | **both** |

Simple picks the Linux shape (`@driver` attribute ≈ `MODULE_DEVICE_TABLE`)
inside an SMF container, reusing the existing loader.
