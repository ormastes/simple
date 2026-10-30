//! Typed interpreter adapters for the native host-capacity ABI.
//! Simple text must be decoded here: the dynamic dispatcher cannot pass a
//! managed interpreter string to runtime_native.c's tagged string ABI.

use crate::error::CompileError;
use crate::value::Value;
use super::common::{get_string, require_args};

#[path = "host_capacity_platform.rs"]
mod platform;

pub fn memory_headroom(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(platform::memory_headroom()))
}

pub fn commit_headroom(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(platform::commit_headroom()))
}

pub fn disk_headroom(args: &[Value]) -> Result<Value, CompileError> {
    const NAME: &str = "rt_host_disk_headroom_bytes_v1";
    require_args(args, 1, NAME)?;
    Ok(Value::Int(platform::disk_headroom(get_string(args, 0, NAME)?)))
}
