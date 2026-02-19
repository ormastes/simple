# File System Utilities Module

Refactored from monolithic `file_system_utils.spl` (1,695 lines) into 8 focused modules.

## Architecture

```
file_system/
├── types.spl          (57 lines)   - Data structures
├── file_ops.spl       (252 lines)  - File operations
├── dir_ops.spl        (335 lines)  - Directory operations
├── path_ops.spl       (248 lines)  - Path manipulation
├── metadata.spl       (208 lines)  - File information
├── permissions.spl    (163 lines)  - Permission management
├── watch.spl          (69 lines)   - File watching
└── utilities.spl      (437 lines)  - Misc utilities
```

## Modules

### types.spl
Core data structures for file system operations.

**Exports:**
- `FileInfo` - File metadata (path, size, times, type, permissions)
- `DirEntry` - Directory entry info
- `Permission` - Unix-style permissions structure
- `TempFile` - Temporary file handle
- `FileWatcher` - File change watcher

### file_ops.spl
Basic file operations with Option/nil error handling.

**Exports:**
- `file_create`, `file_exists`, `file_delete`
- `file_read_text`, `file_read_bytes`, `file_read_lines`
- `file_write_text`, `file_write_bytes`, `file_write_lines`
- `file_append_text`, `file_append_lines`
- `file_rename`, `file_copy`, `file_move`

### dir_ops.spl
Directory operations including recursive walking and copying.

**Exports:**
- `dir_create`, `dir_create_all`, `dir_exists`, `dir_is_empty`
- `dir_list`, `dir_list_detailed`
- `dir_delete`, `dir_delete_all`
- `dir_walk`, `dir_walk_files`, `dir_walk_dirs`
- `dir_copy`, `dir_move`
- `dir_size`, `dir_count_files`, `dir_count_dirs`

### path_ops.spl
Path manipulation (re-exports and extends std.path).

**Exports:**
- `path_join`, `path_join2`, `path_split`
- `path_basename`, `path_dirname`, `path_extension`, `path_stem`
- `path_normalize`, `path_is_absolute`, `path_is_relative`
- `path_resolve`, `path_relative_to`
- `path_with_extension`, `path_has_extension`, `path_common_prefix`

### metadata.spl
File metadata: size, timestamps, type checking.

**Exports:**
- `file_size`, `file_info`
- `file_modified_time`, `file_created_time`, `file_accessed_time`
- `file_is_file`, `file_is_directory`, `file_is_symlink`
- `file_is_readable`, `file_is_writable`, `file_is_executable`, `file_is_hidden`

### permissions.spl
Unix-style permission management.

**Exports:**
- `permission_from_mode`, `permission_to_mode`
- `file_get_permissions`, `file_set_permissions`, `file_set_mode`
- `file_make_readonly`, `file_make_writable`, `file_make_executable`

### watch.spl
File change detection (mock implementation).

**Exports:**
- `watch_create` - Create watcher for path
- `watch_check` - Check if file changed
- `watch_update` - Update watcher timestamp

### utilities.spl
Miscellaneous utilities: temp files, glob, tree ops, symlinks, disk usage.

**Exports:**
- **Temp files:** `temp_file_create`, `temp_file_create_with_name`, `temp_dir_create`, `temp_file_cleanup`
- **Glob:** `glob_match`, `glob_find`, `glob_find_files`, `glob_filter`
- **Tree:** `tree_create`, `tree_print`
- **Symlinks:** `symlink_create`, `symlink_read`, `symlink_resolve`
- **Disk usage:** `disk_usage`, `disk_usage_human`
- **Type detection:** `file_type_from_extension`, `file_mime_type`, `file_is_text`, `file_is_binary`
- **Utilities:** `files_filter_by_extension`, `files_group_by_extension`
- **Counting:** `file_line_count`, `file_word_count`, `file_char_count`

## Usage

### Import entire module (backward compatible)
```simple
use std.file_system_utils

val content = file_system_utils.file_read_text("/path/to/file.txt")
```

### Import specific submodules
```simple
mod file_system.file_ops
mod file_system.dir_ops

val exists = file_ops.file_exists("test.txt")
val entries = dir_ops.dir_list(".")
```

### Direct imports
```simple
use std.file_system_utils.file_read_text
use std.file_system_utils.dir_walk

val content = file_read_text("config.txt")
val files = dir_walk("/home/user")
```

## Design Principles

1. **Pure Simple** - No external dependencies, mock implementations
2. **Option/nil pattern** - No try/catch, all errors return nil
3. **Focused modules** - Each module 200-400 lines with clear responsibility
4. **Backward compatible** - Facade exports all original APIs
5. **No generics** - Uses arrays and tuples for runtime compatibility

## Implementation Notes

- All file I/O operations are **mock implementations** for demonstration
- Real implementations would use SFFI to call platform-specific APIs
- Permission bits use Unix octal format (755, 644, etc.)
- Path operations assume forward-slash separators
- Glob patterns support: `*` (any chars), `?` (one char), `[abc]` (character class)

## Refactoring Stats

- **Before:** 1,695 lines in single file
- **After:** 8 modules (1,769 lines total + 32 line facade)
- **Largest module:** utilities.spl (437 lines)
- **Smallest module:** types.spl (57 lines)
- **Average module size:** 221 lines
