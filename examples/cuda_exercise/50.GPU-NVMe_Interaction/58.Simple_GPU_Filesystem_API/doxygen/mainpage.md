# Module 58: Simple Filesystem Layer

## Overview

This module implements a lightweight filesystem layer for NVMe devices with node-based LBA (Logical Block Address) management. It provides file-level abstractions over raw block storage while maintaining high performance and direct hardware access.

## Key Features

- **Node-based allocation**: Files stored as contiguous LBA ranges (nodes)
- **Template and runtime APIs**: Type-safe template functions and flexible runtime functions
- **Bounds checking**: Automatic validation of all read/write operations
- **File operations**: save, read, write, delete with metadata tracking
- **Garbage collection**: Automatic merging of free space regions
- **C API**: Complete C-compatible wrapper for language interoperability
- **Persistent metadata**: Superblock and file table stored in reserved LBAs

## Architecture

The filesystem is organized into these main components:

### Core Components

- **nvme_simple_fs.h/cpp**: Main C++ filesystem implementation
  - LBA node management
  - File table with metadata
  - Space allocation and garbage collection
  - Template and runtime I/O functions

- **nvme_simple_fs_c_api.h/cpp**: C API wrapper
  - C-compatible function signatures
  - Error handling via error strings
  - Suitable for FFI bindings (Python, Rust, etc.)

### Data Structures

- **Superblock**: Filesystem metadata (magic, version, block counts)
- **LbaNode**: Contiguous LBA range with start, length, file ID
- **FileEntry**: File metadata (name, size, timestamps, checksum)
- **Free list**: Available LBA nodes for allocation

### Memory Layout

```
LBA 0-63:       Metadata region (superblock, file table, node map)
LBA 64-N:       Data region (file contents)
```

## Key APIs

### C++ API

- @ref nvme_fs::NvmeSimpleFilesystem - Main filesystem class
- @ref nvme_fs::NvmeSimpleFilesystem::save_file() - Save file to consecutive LBAs
- @ref nvme_fs::NvmeSimpleFilesystem::read_file() - Read entire file
- @ref nvme_fs::NvmeSimpleFilesystem::write_file() - Write at offset with bounds check
- @ref nvme_fs::NvmeSimpleFilesystem::delete_file() - Delete and free space
- @ref nvme_fs::NvmeSimpleFilesystem::read_node_template() - Template read with type safety
- @ref nvme_fs::NvmeSimpleFilesystem::write_node_template() - Template write with type safety
- @ref nvme_fs::NvmeSimpleFilesystem::read_node() - Runtime read with bounds checking
- @ref nvme_fs::NvmeSimpleFilesystem::write_node() - Runtime write with bounds checking
- @ref nvme_fs::NvmeSimpleFilesystem::garbage_collect() - Merge free nodes

### C API

- @ref nvme_fs_create() - Create new filesystem
- @ref nvme_fs_open() - Open existing filesystem
- @ref nvme_fs_save_file() - Save file
- @ref nvme_fs_read_file() - Read file
- @ref nvme_fs_write_file() - Write at offset
- @ref nvme_fs_delete_file() - Delete file
- @ref nvme_fs_read_node() - Node-based read
- @ref nvme_fs_write_node() - Node-based write
- @ref nvme_fs_garbage_collect() - Run GC

## Usage Examples

### Basic File Operations (C++)

```cpp
#include "nvme_simple_fs.h"

// Create filesystem
auto fs = nvme_fs::create_filesystem(nvme_device, 0, 1000000, 512);

// Save file
std::vector<uint8_t> data(4096, 0xAB);
fs->save_file("test.bin", data.data(), data.size());

// Read file
std::vector<uint8_t> buffer(4096);
fs->read_file("test.bin", buffer.data(), buffer.size());

// Write at offset
std::vector<uint8_t> patch(512, 0xCD);
fs->write_file("test.bin", 1024, patch.data(), patch.size());
```

### Node-based I/O with Templates (C++)

```cpp
// Get LBA node for file
auto node = fs->get_file_node("data.bin");

// Type-safe read
std::vector<float> values(256);
fs->read_node_template<float>(node, 0, values.data(), values.size());

// Type-safe write
std::vector<double> results(128);
fs->write_node_template<double>(node, 1024, results.data(), results.size());
```

### C API Usage

```c
#include "nvme_simple_fs_c_api.h"

// Create filesystem
nvme_fs_handle_t* fs = nvme_fs_create(nvme_device, 0, 1000000, 512);

// Save file
uint8_t data[2048];
nvme_fs_save_file(fs, "file.bin", data, sizeof(data));

// Get file info
nvme_fs_file_info_t info;
nvme_fs_get_file_info(fs, "file.bin", &info);

// Read via node
nvme_fs_node_t node;
nvme_fs_get_file_node(fs, "file.bin", &node);
nvme_fs_read_node(fs, &node, 512, buffer, 1024);

// Cleanup
nvme_fs_close(fs);
```

## Error Handling

The C++ API uses exceptions:
- `nvme_fs::FileNotFoundError` - File doesn't exist
- `nvme_fs::OutOfSpaceError` - Insufficient consecutive space
- `nvme_fs::AccessViolationError` - Read/write out of bounds

The C API uses return codes and error strings:
- Return 0 on success, negative on error
- Use `nvme_fs_get_last_error()` for error messages

## Testing

See test/ directory for comprehensive unit tests covering:
- Basic file operations
- Node-based I/O
- Template API usage
- Bounds checking
- Garbage collection
- C API wrapper

## Performance Considerations

- **Consecutive allocation**: Files stored in contiguous LBAs for optimal read performance
- **Metadata caching**: All metadata kept in memory, flushed on demand
- **Block-aligned I/O**: Unaligned access uses read-modify-write
- **No fragmentation initially**: First-fit allocation minimizes fragmentation
- **Periodic GC**: Run garbage_collect() after deletions to merge free space

## Future Enhancements

- Wear leveling for NVMe SSDs
- Compression support
- Encryption at rest
- Directory hierarchy support
- Journaling for crash recovery
