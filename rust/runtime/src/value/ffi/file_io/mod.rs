//! File I/O FFI functions for Simple runtime.
//!
//! This module provides comprehensive file system operations organized into submodules:
//!
//! ## Submodules
//!
//! - **metadata**: File metadata and existence checks
//!   - rt_file_exists, rt_file_stat
//!
//! - **file_ops**: High-level file operations
//!   - rt_file_canonicalize, rt_file_read_text, rt_file_write_text
//!   - rt_file_copy, rt_file_remove, rt_file_rename
//!
//! - **directory**: Directory operations
//!   - rt_dir_create, rt_dir_list, rt_dir_remove
//!   - rt_file_find, rt_dir_glob
//!
//! - **descriptor**: Low-level file descriptor operations
//!   - rt_file_open, rt_file_get_size, rt_file_close
//!
//! - **mmap**: Memory-mapped I/O (Unix-specific)
//!   - rt_file_mmap, rt_file_munmap, rt_file_madvise, rt_file_msync
//!
//! - **path**: Path manipulation utilities
//!   - rt_path_basename, rt_path_dirname, rt_path_ext
//!   - rt_path_absolute, rt_path_separator

// Module declarations
pub mod metadata;
pub mod file_ops;
pub mod directory;
pub mod descriptor;
pub mod mmap;
pub mod path;

// Re-export all public functions for compatibility
pub use metadata::{rt_file_exists, rt_file_stat};
pub use file_ops::{
    rt_file_canonicalize, rt_file_read_text, rt_file_read_text_rv, rt_file_write_text, rt_file_copy, rt_file_remove,
    rt_file_rename, rt_file_read_lines, rt_file_append_text, rt_file_read_bytes, rt_file_write_bytes, rt_file_move,
};
pub use directory::{
    rt_dir_create, rt_dir_list, rt_dir_remove, rt_file_find, rt_dir_glob, rt_dir_create_all, rt_dir_walk,
    rt_current_dir, rt_set_current_dir, rt_dir_remove_all,
};
pub use descriptor::{rt_file_open, rt_file_get_size, rt_file_close};
pub use mmap::{rt_file_mmap, rt_file_munmap, rt_file_madvise, rt_file_msync, native_msync};
pub use path::{
    rt_path_basename, rt_path_dirname, rt_path_ext, rt_path_absolute, rt_path_separator, rt_path_stem,
    rt_path_relative, rt_path_join,
};
