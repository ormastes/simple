//! Filesystem operations extern functions
//!
//! Native filesystem and file operations for Simple language.
//! All operations delegate to the native I/O layer (interpreter_native_io).

use crate::error::CompileError;
use crate::value::Value;
use super::super::interpreter_native_io as native_io;

// ============================================================================
// Filesystem Operations (fs_*)
// ============================================================================

/// Check if file or directory exists
///
/// No effect check - read-only query
pub fn native_fs_exists(args: &[Value]) -> Result<Value, CompileError> {
    native_io::native_fs_exists(args)
}

/// Read file as bytes
///
/// # Effect
/// * Requires filesystem read effect
pub fn native_fs_read(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_fs_read")?;
    native_io::native_fs_read(args)
}

/// Read file as string
///
/// # Effect
/// * Requires filesystem read effect
pub fn native_fs_read_string(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_fs_read_string")?;
    native_io::native_fs_read_string(args)
}

/// Write bytes to file
///
/// # Effect
/// * Requires filesystem write effect
pub fn native_fs_write(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_fs_write")?;
    native_io::native_fs_write(args)
}

/// Write string to file
///
/// # Effect
/// * Requires filesystem write effect
pub fn native_fs_write_string(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_fs_write_string")?;
    native_io::native_fs_write_string(args)
}

/// Append bytes to file
///
/// # Effect
/// * Requires filesystem write effect
pub fn native_fs_append(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_fs_append")?;
    native_io::native_fs_append(args)
}

/// Create directory
///
/// # Effect
/// * Requires filesystem write effect
pub fn native_fs_create_dir(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_fs_create_dir")?;
    native_io::native_fs_create_dir(args)
}

/// Remove file
///
/// # Effect
/// * Requires filesystem write effect
pub fn native_fs_remove_file(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_fs_remove_file")?;
    native_io::native_fs_remove_file(args)
}

/// Remove directory
///
/// # Effect
/// * Requires filesystem write effect
pub fn native_fs_remove_dir(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_fs_remove_dir")?;
    native_io::native_fs_remove_dir(args)
}

/// Rename/move file or directory
///
/// # Effect
/// * Requires filesystem write effect
pub fn native_fs_rename(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_fs_rename")?;
    native_io::native_fs_rename(args)
}

/// Copy file
///
/// # Effect
/// * Requires filesystem write effect
pub fn native_fs_copy(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_fs_copy")?;
    native_io::native_fs_copy(args)
}

/// Get file metadata
///
/// # Effect
/// * Requires filesystem read effect
pub fn native_fs_metadata(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_fs_metadata")?;
    native_io::native_fs_metadata(args)
}

/// Read directory entries
///
/// # Effect
/// * Requires filesystem read effect
pub fn native_fs_read_dir(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_fs_read_dir")?;
    native_io::native_fs_read_dir(args)
}

/// Open file handle
///
/// # Effect
/// * Requires filesystem read effect
pub fn native_fs_open(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_fs_open")?;
    native_io::native_fs_open(args)
}

// ============================================================================
// File Operations (file_*)
// ============================================================================

/// Read from file handle
///
/// # Effect
/// * Requires filesystem read effect
pub fn native_file_read(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_file_read")?;
    native_io::native_file_read(args)
}

/// Write to file handle
///
/// # Effect
/// * Requires filesystem write effect
pub fn native_file_write(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_file_write")?;
    native_io::native_file_write(args)
}

/// Flush file handle
///
/// # Effect
/// * Requires filesystem write effect
pub fn native_file_flush(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_file_flush")?;
    native_io::native_file_flush(args)
}

/// Seek in file handle
///
/// # Effect
/// * Requires filesystem read effect
pub fn native_file_seek(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_file_seek")?;
    native_io::native_file_seek(args)
}

/// Sync file handle to disk
///
/// # Effect
/// * Requires filesystem write effect
pub fn native_file_sync(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_file_sync")?;
    native_io::native_file_sync(args)
}

/// Close file handle
///
/// # Effect
/// * Requires filesystem write effect
pub fn native_file_close(args: &[Value]) -> Result<Value, CompileError> {
    use crate::effects::check_effect_violations;
    check_effect_violations("native_file_close")?;
    native_io::native_file_close(args)
}
