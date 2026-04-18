# Authoring a Simple Driver

> Companion: `doc/04_architecture/driver_architecture.md`.
> Trait definition: `src/lib/nogc_sync_mut/driver/core.spl`.

A driver in Simple is one `.spl` module that (a) declares a manifest via
`@driver(...)`, and (b) implements the `Driver` trait. The same source is
compiled into the kernel statically **or** packaged as an `.lsm` loadable
module — the build profile picks, you do not change the source.

## 1. Minimum viable driver

```spl
# examples/simple_os/drivers/null_block/null_block.spl
use std.driver.core.{Driver}
use std.driver.error.{DriverError}
use std.driver.types.{DriverContext, DriverHandle, DeviceId, IoctlCmd,
                      ProbeResult, PowerState, DriverClass}

@driver(class = DriverClass.Block,
        vendor = 0x0000,
        device = [0x0000],
        version = "0.1")
module null_block:

    struct NullBlock:
        attached: i32

    impl Driver for NullBlock:

        fn manifest_abi_rev() -> i32:
            return 1

        fn init(ctx: DriverContext) -> Result<(), DriverError>:
            return Result.Ok(())

        fn probe(dev: DeviceId) -> Result<ProbeResult, DriverError>:
            # Match anything. Real drivers check dev.value against the
            # vendor/device list in the manifest. Device class is exposed
            # on DeviceId as `dev.dclass` (not `class` — keyword clash).
            return Result.Ok(ProbeResult.Accept)

        fn attach(dev: DeviceId) -> Result<DriverHandle, DriverError>:
            return Result.Ok(DriverHandle(value: dev.value))

        fn detach(h: DriverHandle) -> Result<(), DriverError>:
            return Result.Ok(())

        fn suspend(h: DriverHandle, state: PowerState) -> Result<(), DriverError>:
            return Result.Ok(())

        fn resume(h: DriverHandle) -> Result<(), DriverError>:
            return Result.Ok(())

        fn ioctl(h: DriverHandle, cmd: IoctlCmd) -> Result<i64, DriverError>:
            return Result.Err(DriverError.NotSupported)
```

Build static (kernel-embedded):
```
bin/simple build --driver-mode=static  examples/simple_os/drivers/null_block
```

Build dynamic (loadable `.lsm`):
```
bin/simple build --driver-mode=dynamic examples/simple_os/drivers/null_block
```

## 2. MMIO, IRQs, bitmasks

MMIO goes through `std.io.volatile_ops`:

```spl
use std.io.volatile_ops.{volatile_read_u32, volatile_write_u32, memory_barrier}

var CTRL_REG_ENABLE: i32 = 0x1 << 0
var CTRL_REG_RESET:  i32 = 0x1 << 1
var CTRL_REG_IRQ_EN: i32 = 0x1 << 4

fn enable(base: i64):
    var v: i32 = volatile_read_u32(base + 0x00)
    v = v | CTRL_REG_ENABLE | CTRL_REG_IRQ_EN
    memory_barrier()
    volatile_write_u32(base + 0x00, v)
```

Bitwise operators (`&`, `|`, `^`, `~`, `<<`, `>>`) work in the language.
(Phase C adds bitfield-struct sugar that lowers to these ops.)

Interrupt handlers declare the `@interrupt` attribute:

```spl
@interrupt fn irq_handler(vec: u8):
    # minimal ISR: ack, schedule bottom half, return
    ...
```

## 3. C drivers: write a Simple shim

Legal, but the `@driver` manifest must still be in the `.spl` shim, and
the shim must implement `Driver`:

```spl
@driver(class = DriverClass.Block, vendor = 0x1B36, device = [0x000E], version = "1.0")
module legacy_nvme_shim:

    extern fn c_nvme_driver_init(ctx: i64) -> i32
    extern fn c_nvme_driver_attach(bdf: i64) -> i64

    struct LegacyNvme:
        dummy: i32

    impl Driver for LegacyNvme:
        fn manifest_abi_rev() -> i32 = 1

        fn init(ctx: DriverContext) -> Result<(), DriverError>:
            var rc: i32 = c_nvme_driver_init(ctx.opaque)
            match rc:
                0 -> return Result.Ok(())
                _ -> return Result.Err(DriverError.IoError)
        # ... remaining ops delegate similarly ...
```

`sffi_lint` (Phase B) rejects any driver module that declares `extern fn`
without a matching `impl Driver`.

## 4. Testing

Unit-test a driver by constructing its struct directly and calling trait
methods — no loader needed:

```spl
# test/drivers/null_block_test.spl
use std.driver.core.{Driver}
use std.driver.types.{DriverContext, DeviceId, DriverClass, ProbeResult}
use examples.simple_os.drivers.null_block.{NullBlock}

describe "null_block":
    it "accepts any probe":
        var d: NullBlock = NullBlock(attached: 0)
        var ctx: DriverContext = DriverContext(opaque: 0)
        d.init(ctx)
        var r = d.probe(DeviceId(value: 0, dclass: DriverClass.Block))
        assert(r == Result.Ok(ProbeResult.Accept))
```

(Use `std.io_runtime` for any I/O in tests — not `app.io` — see
`feedback_test_imports.md`.)

## 5. Pure-Simple first — what you must not do

- Do not call `extern fn` for anything you could write in pure Simple
  (bitmasks, MMIO helpers, endian conversion, state machines).
- Do not smuggle heap allocations into a no-alloc driver path — stay in
  `std.lib.nogc_sync_mut.*` unless the device class genuinely needs GC.
- Do not bypass the `Driver` trait — the loader will refuse to register
  a module that has `@driver(...)` without the trait impl.
- Do not create branches (per repo VCS rule). Drivers land on `main`.

## 6. Current limitations (Phase A status)

- The loader does not yet exist (Phase B). For now the trait compiles but
  is reachable only from static-mode builds that call the driver struct
  directly.
- Native bitfield syntax is not in yet (Phase C) — use shift-and-mask.
- DMA-coherent-alloc is not in yet (Phase C) — use barriers + manual
  allocation.
- Known issue: Cranelift `>>` backend bug (see `feedback_cranelift_shr_bug.md`).
  Fixed in Phase C.
