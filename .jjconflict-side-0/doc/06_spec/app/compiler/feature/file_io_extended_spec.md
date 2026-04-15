# Extended File I/O Specification

**Feature ID:** #700-715 | **Category:** Infrastructure | **Status:** Implemented

_Source: `test/feature/usage/file_io_extended_spec.spl`_

---

Extended File I/O operations including line-based reading, append operations,
binary I/O, file moving, recursive directory operations, and path utilities.

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 20 |

## Test Structure

### read_lines

- ✅ reads multiple lines correctly
- ✅ reads empty file as empty list
### append_file

- ✅ appends to existing file
- ✅ creates file if not exists
### binary I/O

- ✅ preserves binary data exactly
### move_file

- ✅ moves file to new location
### create_dir_all

- ✅ creates nested directories
### walk_dir

- ✅ returns all files recursively
### current_dir and set_current_dir

- ✅ gets absolute path
### remove_dir_all

- ✅ removes directory and contents
### stem

- ✅ extracts filename without extension
- ✅ handles multiple dots
- ✅ handles no extension
### relative_path

- ✅ computes relative path
- ✅ handles same path
### path_join

- ✅ joins two paths
### Error Handling

- ✅ read_lines fails for non-existent file
- ✅ read_bytes fails for non-existent file
- ✅ move_file fails for non-existent source
- ✅ walk_dir fails for non-existent directory

