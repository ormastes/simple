# Native File and Directory Operations Tests

**Feature ID:** #IO-001 | **Category:** I/O | **Status:** Active

_Sources:_
- `test/integration/io/native_ops_file_read_write_spec.spl`
- `test/integration/io/native_ops_file_copy_spec.spl`
- `test/integration/io/native_ops_file_size_spec.spl`
- `test/integration/io/native_ops_dir_create_spec.spl`
- `test/integration/io/native_ops_dir_recursive_spec.spl`
- `test/integration/io/native_ops_dir_create_all_spec.spl`

---

## Overview

Tests native file and directory operations using SFFI without shell fallbacks. Validates
file creation, reading, copying, size retrieval, and deletion via file_ops, as well as
directory creation (including recursive/nested), directory detection, and removal via dir_ops.
All operations use /tmp paths and clean up after themselves.

## Syntax

```simple
file_write(test_file, content)
val read_content = file_read(test_file)
expect(read_content).to_equal(content)
file_delete(test_file)

dir_create(test_dir, true)  # recursive
check(is_dir(test_dir))
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 6 |

## Test Structure

### Native File Operations

- ✅ creates and reads files
- ✅ copies files
- ✅ gets file size

### Native Directory Operations

- ✅ creates directories
- ✅ creates nested directories recursively
- ✅ creates directory tree with dir_create_all
