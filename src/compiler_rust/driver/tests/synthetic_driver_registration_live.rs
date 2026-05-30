#![cfg(target_arch = "x86_64")]

use simple_driver::runner::Runner;
use std::fs;
use tempfile::tempdir;

const SYNTHETIC_DRIVER_SOURCE: &str = r#"
use std.driver.error.{DriverError}
use std.driver.manifest.{DriverManifest, DRVS_ABI_REV}
use std.driver.registry.{DriverOps}
use std.driver.static_table.{register_static_driver, static_driver_count}
use std.driver.types.{DriverClass, DriverHandle, DriverContext, DeviceId, IoctlCmd, PowerState, ProbeResult}

fn synth_abi_rev() -> i32:
    DRVS_ABI_REV

fn synth_init(ctx: DriverContext) -> Result<(), DriverError>:
    Ok(())

fn synth_probe(dev: DeviceId) -> Result<ProbeResult, DriverError>:
    Ok(ProbeResult.Accept)

fn synth_attach(dev: DeviceId) -> Result<DriverHandle, DriverError>:
    Ok(DriverHandle(value: 1))

fn synth_detach(h: DriverHandle) -> Result<(), DriverError>:
    Ok(())

fn synth_suspend(h: DriverHandle, s: PowerState) -> Result<(), DriverError>:
    Ok(())

fn synth_resume(h: DriverHandle) -> Result<(), DriverError>:
    Ok(())

fn synth_ioctl(h: DriverHandle, cmd: IoctlCmd) -> Result<i64, DriverError>:
    Ok(0)

fn synth_ops() -> DriverOps:
    DriverOps(
        self_ptr: 0,
        manifest_abi: synth_abi_rev,
        init_fn: synth_init,
        probe_fn: synth_probe,
        attach_fn: synth_attach,
        detach_fn: synth_detach,
        suspend_fn: synth_suspend,
        resume_fn: synth_resume,
        ioctl_fn: synth_ioctl,
    )

@driver(class=DriverClass.Block, vendor=0x1234, device=[0x5678], version="9.9", ops=synth_ops())
fn register_synth_driver() -> Result<i32, DriverError>:
    todo("FR-DRIVER-0001 synthetic registration body", "compiler replaces this stub before HIR execution")

fn main() -> i32:
    val before = static_driver_count()
    match register_synth_driver():
        Ok(_) -> return static_driver_count() - before
        Err(_) -> return -7
"#;

#[test]
fn driver_attr_ops_stub_executes_synthesized_static_registration() {
    let dir = tempdir().expect("tempdir");
    let source = dir.path().join("synthetic_driver_registration.spl");
    fs::write(&source, SYNTHETIC_DRIVER_SOURCE).expect("write source");

    let runner = Runner::new();
    let exit = runner.run_file(&source).expect("run synthetic driver registration");

    assert_eq!(
        exit, 1,
        "stub-only @driver(..., ops=...) function should synthesize and execute register_static_driver"
    );
}

const SYNTHETIC_NATIVE_LIB_SOURCE: &str = r#"
use std.driver.error.{DriverError}
use std.driver.manifest.{DriverManifest, DRVS_ABI_REV}
use std.driver.registry.{DriverOps}
use std.driver.static_table.{register_static_driver, static_driver_count}
use std.driver.types.{DriverHandle, DriverContext, DeviceId, IoctlCmd, PowerState, ProbeResult}

fn synth_abi_rev() -> i32:
    DRVS_ABI_REV

fn synth_init(ctx: DriverContext) -> Result<(), DriverError>:
    Ok(())

fn synth_probe(dev: DeviceId) -> Result<ProbeResult, DriverError>:
    Ok(ProbeResult.Accept)

fn synth_attach(dev: DeviceId) -> Result<DriverHandle, DriverError>:
    Ok(DriverHandle(value: 2))

fn synth_detach(h: DriverHandle) -> Result<(), DriverError>:
    Ok(())

fn synth_suspend(h: DriverHandle, s: PowerState) -> Result<(), DriverError>:
    Ok(())

fn synth_resume(h: DriverHandle) -> Result<(), DriverError>:
    Ok(())

fn synth_ioctl(h: DriverHandle, cmd: IoctlCmd) -> Result<i64, DriverError>:
    Ok(0)

fn synth_ops() -> DriverOps:
    DriverOps(
        self_ptr: 0,
        manifest_abi: synth_abi_rev,
        init_fn: synth_init,
        probe_fn: synth_probe,
        attach_fn: synth_attach,
        detach_fn: synth_detach,
        suspend_fn: synth_suspend,
        resume_fn: synth_resume,
        ioctl_fn: synth_ioctl,
    )

@native_lib("simple", "7.7", ops=synth_ops())
fn register_synth_native_lib() -> Result<i32, DriverError>:
    todo("FR-DRIVER-0001 native-lib synthetic registration body", "compiler replaces this stub before HIR execution")

fn main() -> i32:
    val before = static_driver_count()
    match register_synth_native_lib():
        Ok(_) -> return static_driver_count() - before
        Err(_) -> return -7
"#;

#[test]
fn native_lib_attr_ops_stub_executes_synthesized_static_registration() {
    let dir = tempdir().expect("tempdir");
    let source = dir.path().join("synthetic_native_lib_registration.spl");
    fs::write(&source, SYNTHETIC_NATIVE_LIB_SOURCE).expect("write source");

    let runner = Runner::new();
    let exit = runner.run_file(&source).expect("run synthetic native-lib registration");

    assert_eq!(
        exit, 1,
        "stub-only @native_lib(..., ops=...) function should synthesize and execute register_static_driver"
    );
}

const IMPL_LEVEL_DRIVER_SOURCE: &str = r#"
use std.driver.error.{DriverError}
use std.driver.manifest.{DriverManifest, DRVS_ABI_REV}
use std.driver.registry.{DriverOps}
use std.driver.static_table.{register_static_driver, static_driver_count}
use std.driver.types.{DriverClass, DriverHandle, DriverContext, DeviceId, IoctlCmd, PowerState, ProbeResult}

struct ImplSynthDriver:
    marker: i32

fn synth_abi_rev() -> i32:
    DRVS_ABI_REV
fn synth_init(ctx: DriverContext) -> Result<(), DriverError>:
    Ok(())
fn synth_probe(dev: DeviceId) -> Result<ProbeResult, DriverError>:
    Ok(ProbeResult.Accept)
fn synth_attach(dev: DeviceId) -> Result<DriverHandle, DriverError>:
    Ok(DriverHandle(value: 3))
fn synth_detach(h: DriverHandle) -> Result<(), DriverError>:
    Ok(())
fn synth_suspend(h: DriverHandle, s: PowerState) -> Result<(), DriverError>:
    Ok(())
fn synth_resume(h: DriverHandle) -> Result<(), DriverError>:
    Ok(())
fn synth_ioctl(h: DriverHandle, cmd: IoctlCmd) -> Result<i64, DriverError>:
    Ok(0)
fn synth_ops() -> DriverOps:
    DriverOps(self_ptr: 0, manifest_abi: synth_abi_rev, init_fn: synth_init, probe_fn: synth_probe, attach_fn: synth_attach, detach_fn: synth_detach, suspend_fn: synth_suspend, resume_fn: synth_resume, ioctl_fn: synth_ioctl)

@driver(class=DriverClass.Block, vendor=0x1234, device=[0x5678], version="9.9", ops=synth_ops())
impl ImplSynthDriver:
    static fn register_synth_driver() -> Result<i32, DriverError>:
        todo("FR-DRIVER-0001 impl synthetic registration body", "compiler inherits impl manifest attrs")

fn main() -> i32:
    val before = static_driver_count()
    match ImplSynthDriver.register_synth_driver():
        Ok(_) -> return static_driver_count() - before
        Err(_) -> return -7
"#;

#[test]
fn impl_level_driver_attr_ops_stub_executes_synthesized_static_registration() {
    let dir = tempdir().expect("tempdir");
    let source = dir.path().join("synthetic_impl_driver_registration.spl");
    fs::write(&source, IMPL_LEVEL_DRIVER_SOURCE).expect("write source");

    let runner = Runner::new();
    let exit = runner.run_file(&source).expect("run synthetic impl driver registration");

    assert_eq!(
        exit, 1,
        "stub-only method under @driver(..., ops=...) impl should synthesize register_static_driver"
    );
}

const IMPL_LEVEL_NATIVE_LIB_SOURCE: &str = r#"
use std.driver.error.{DriverError}
use std.driver.manifest.{DriverManifest, DRVS_ABI_REV}
use std.driver.registry.{DriverOps}
use std.driver.static_table.{register_static_driver, static_driver_count}
use std.driver.types.{DriverHandle, DriverContext, DeviceId, IoctlCmd, PowerState, ProbeResult}

struct ImplSynthNative:
    marker: i32

fn synth_abi_rev() -> i32:
    DRVS_ABI_REV
fn synth_init(ctx: DriverContext) -> Result<(), DriverError>:
    Ok(())
fn synth_probe(dev: DeviceId) -> Result<ProbeResult, DriverError>:
    Ok(ProbeResult.Accept)
fn synth_attach(dev: DeviceId) -> Result<DriverHandle, DriverError>:
    Ok(DriverHandle(value: 4))
fn synth_detach(h: DriverHandle) -> Result<(), DriverError>:
    Ok(())
fn synth_suspend(h: DriverHandle, s: PowerState) -> Result<(), DriverError>:
    Ok(())
fn synth_resume(h: DriverHandle) -> Result<(), DriverError>:
    Ok(())
fn synth_ioctl(h: DriverHandle, cmd: IoctlCmd) -> Result<i64, DriverError>:
    Ok(0)
fn synth_ops() -> DriverOps:
    DriverOps(self_ptr: 0, manifest_abi: synth_abi_rev, init_fn: synth_init, probe_fn: synth_probe, attach_fn: synth_attach, detach_fn: synth_detach, suspend_fn: synth_suspend, resume_fn: synth_resume, ioctl_fn: synth_ioctl)

@native_lib("simple", "7.7", ops=synth_ops())
impl ImplSynthNative:
    static fn register_synth_native_lib() -> Result<i32, DriverError>:
        todo("FR-DRIVER-0001 impl native-lib synthetic registration body", "compiler inherits impl manifest attrs")

fn main() -> i32:
    val before = static_driver_count()
    match ImplSynthNative.register_synth_native_lib():
        Ok(_) -> return static_driver_count() - before
        Err(_) -> return -7
"#;

#[test]
fn impl_level_native_lib_attr_ops_stub_executes_synthesized_static_registration() {
    let dir = tempdir().expect("tempdir");
    let source = dir.path().join("synthetic_impl_native_lib_registration.spl");
    fs::write(&source, IMPL_LEVEL_NATIVE_LIB_SOURCE).expect("write source");

    let runner = Runner::new();
    let exit = runner.run_file(&source).expect("run synthetic impl native-lib registration");

    assert_eq!(
        exit, 1,
        "stub-only method under @native_lib(..., ops=...) impl should synthesize register_static_driver"
    );
}
