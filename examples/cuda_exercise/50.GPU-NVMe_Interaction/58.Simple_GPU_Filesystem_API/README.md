# 🎯 Part 58: Simple GPU Filesystem API

**Goal**: Implement a lightweight filesystem with node-based LBA management, providing file operations with bounds-checked read/write, garbage collection, and both C++ template/runtime APIs and a C API wrapper.

**Architecture**: High-level filesystem abstraction built on Module 53's NVMe infrastructure

**GPU Buffer Default**: Uses the **Default GPU Buffer** layout (host SQ/CQ/PRP, GPU data/pool). The legacy **Naive GPU Buffer** (all GPU) lives only in Module 56 and is not used here.

**Note**: This module provides a **dictionary-style API** for structured data access over NVMe storage. It builds on Module 53's VFIO NVMe driver and buffer management infrastructure. For raw NVMe I/O operations, see Module 53. For performance benchmarks of the underlying I/O modes, see Module 53 Section 53.8 and Module 57.

## Project Structure

```
58.Simple_GPU_Filesystem_API/
├── README.md          - This documentation
├── CMakeLists.txt     - Build configuration
├── doxygen/           - API documentation
│   ├── Doxyfile.in   - Doxygen configuration
│   └── mainpage.md   - Main documentation page
├── src/               - Source implementations
│   ├── common/        - Headers
│   │   ├── nvme_simple_fs.h         - Main C++ filesystem API
│   │   └── nvme_simple_fs_c_api.h   - C API wrapper
│   └── host/          - Implementations
│       ├── nvme_simple_fs.cpp       - Filesystem implementation
│       └── nvme_simple_fs_c_api.cpp - C API wrapper implementation
└── test/              - Test files
    └── unit/
        └── host/
            ├── test_filesystem_basic.cpp - Core filesystem tests
            └── test_c_api.cpp            - C API wrapper tests
```

## Quick Navigation

- [58.1 Filesystem Architecture](#581-filesystem-architecture)
- [58.2 LBA Node Management](#582-lba-node-management)
- [58.3 File Operations](#583-file-operations)
- [58.4 Node-based I/O (Template and Runtime)](#584-node-based-io-template-and-runtime)
- [58.5 Garbage Collection](#585-garbage-collection)
- [58.6 C API Wrapper](#586-c-api-wrapper)
- [58.7 Testing](#587-testing)
- [Build & Run](#build--run)
- [Summary](#summary)
- **Performance**: See [Module 53 Section 53.8](../53.NVMe_VFIO_Host_Layer/README.md#538-performance-testing) for underlying I/O performance

---

## Recent Updates (2025-11-05)
- `save_file` now pads partially filled blocks before calling `write_blocks`, preventing over-reads when file sizes are not exact multiples of the NVMe block size.
- The change preserves checksum validation by computing CRC32 on the original payload and only padding the alignment buffer.

## **58.1 Filesystem Architecture**

This section introduces the overall design of the simple filesystem, which manages files as contiguous LBA (Logical Block Address) nodes. The filesystem provides a high-level abstraction over raw NVMe block storage while maintaining performance and direct hardware access.

### **58.1.1 Design Principles**

The filesystem is designed with these key principles:

1. **Simplicity**: Minimal metadata overhead, straightforward allocation strategy
2. **Performance**: Consecutive LBA allocation for sequential access patterns
3. **Safety**: Bounds checking on all read/write operations to prevent data corruption
4. **Flexibility**: Both compile-time template APIs and runtime APIs for different use cases

The filesystem stores metadata (superblock, file table, node map) in reserved LBAs at the beginning of the storage region, with file data stored in subsequent blocks.

### **58.1.2 Metadata Structure**

Core data structures are defined in `src/common/nvme_simple_fs.h`:

```cpp
// Filesystem superblock (stored in LBA 0)
struct Superblock {
    std::uint32_t magic{0x4E564653};  // "NVFS"
    std::uint32_t version{1};
    std::uint64_t total_blocks{0};
    std::uint64_t block_size{512};
    std::uint64_t metadata_blocks{64}; // Blocks reserved for metadata
    std::uint64_t next_file_id{1};
    std::uint32_t num_files{0};
    std::uint32_t num_nodes{0};
};

// LBA node representing a file or free space
struct LbaNode {
    std::uint64_t start_lba{0};
    std::uint64_t length{0};     // Number of blocks
    std::uint32_t file_id{0};    // 0 = free space
    std::uint32_t flags{0};

    bool is_free() const { return file_id == 0; }
    std::uint64_t end_lba() const { return start_lba + length; }
};

// File metadata entry
struct FileEntry {
    std::string   name;
    std::uint32_t file_id{0};
    std::uint64_t size_bytes{0};
    std::uint64_t created_time{0};
    std::uint64_t modified_time{0};
    std::uint32_t checksum{0};   // CRC32 checksum
};
```

**Memory Layout:**
```
LBA 0:        Superblock (magic, version, block counts)
LBA 1-63:     File table and node map
LBA 64-N:     File data region
```

Source: `src/common/nvme_simple_fs.h:30-64`

### **58.1.3 Filesystem Initialization**

Creating or opening a filesystem (from `src/host/nvme_simple_fs.cpp`):

```cpp
// Create new filesystem
auto fs = nvme_fs::create_filesystem(
    nvme_device,     // NVMe device handle from Module 53
    0,               // Starting LBA
    1000000,         // Total blocks (1M blocks = ~512 MB at 512B/block)
    512              // Block size
);

// Open existing filesystem
auto fs = nvme_fs::open_filesystem(nvme_device, 0);
```

The constructor attempts to load existing metadata; if none is found (invalid magic number), it formats a new filesystem with one large free node.

Source: `src/host/nvme_simple_fs.cpp:48-71`

---

## **58.2 LBA Node Management**

This section describes how the filesystem manages storage space using LBA nodes. Each node represents a contiguous range of logical blocks, either allocated to a file or marked as free space.

### **58.2.1 Node Allocation Strategy**

The filesystem uses a **first-fit allocation** strategy: when allocating space for a new file, it searches the free list for the first node large enough to satisfy the request.

```cpp
LbaNode NvmeSimpleFilesystem::allocate_space(std::uint64_t size_bytes) {
    // Calculate required blocks
    std::uint64_t required_blocks =
        (size_bytes + superblock_.block_size - 1) / superblock_.block_size;

    // Find first-fit free node
    for (auto it = free_list_.begin(); it != free_list_.end(); ++it) {
        if (it->length >= required_blocks) {
            LbaNode allocated;
            allocated.start_lba = it->start_lba;
            allocated.length = required_blocks;
            allocated.file_id = superblock_.next_file_id++;

            // Update or remove free node
            if (it->length == required_blocks) {
                free_list_.erase(it);
            } else {
                it->start_lba += required_blocks;
                it->length -= required_blocks;
            }

            return allocated;
        }
    }

    throw OutOfSpaceError("Insufficient consecutive space for allocation");
}
```

Source: `src/host/nvme_simple_fs.cpp:176-203`

**Key Points:**
- Files are allocated in consecutive LBAs for optimal sequential read performance
- Allocation fails if no single contiguous region is large enough
- After allocation, the free node is split or removed from the free list

### **58.2.2 Free Space Tracking**

When a file is deleted, its LBA node is marked as free and added to the free list:

```cpp
void NvmeSimpleFilesystem::free_space(const LbaNode& node) {
    LbaNode free_node = node;
    free_node.file_id = 0;  // Mark as free
    free_list_.push_back(free_node);
    // Note: garbage_collect() will merge adjacent free nodes later
}
```

Source: `src/host/nvme_simple_fs.cpp:205-209`

The free list maintains all unallocated LBA ranges. Adjacent free nodes are merged during garbage collection to reduce fragmentation.

---

## **58.3 File Operations**

This section covers the high-level file operations: saving, reading, writing, and deleting files. These operations provide familiar filesystem semantics while managing LBA nodes internally.

### **58.3.1 Saving Files**

The `save_file()` function allocates consecutive LBAs and writes file data:

```cpp
std::uint32_t save_file(const std::string& filename,
                        const void* data,
                        std::size_t size_bytes) {
    // Check if file already exists
    if (file_table_.find(filename) != file_table_.end()) {
        throw std::runtime_error("File already exists: " + filename);
    }

    // Allocate consecutive LBAs
    LbaNode node = allocate_space(size_bytes);

    // Write data to NVMe
    NvmeDevice* dev = static_cast<NvmeDevice*>(nvme_device_);
    nvme_host::write_blocks(dev, node.start_lba, node.length, data);

    // Create file entry
    FileEntry entry;
    entry.name = filename;
    entry.file_id = node.file_id;
    entry.size_bytes = size_bytes;
    entry.created_time = get_current_timestamp();
    entry.modified_time = entry.created_time;
    entry.checksum = calculate_crc32(data, size_bytes);

    file_table_[filename] = entry;
    node_map_[node.file_id] = node;

    save_metadata();
    return node.file_id;
}
```

Source: `src/host/nvme_simple_fs.cpp:230-256`

**Usage:**
```cpp
std::vector<std::uint8_t> data(4096, 0xAB);
std::uint32_t file_id = fs->save_file("test.bin", data.data(), data.size());
```

### **58.3.2 Reading Files**

The `read_file()` function reads an entire file into a buffer:

```cpp
std::size_t read_file(const std::string& filename,
                      void* buffer,
                      std::size_t buffer_size) {
    auto it = file_table_.find(filename);
    if (it == file_table_.end()) {
        throw FileNotFoundError("File not found: " + filename);
    }

    const FileEntry& entry = it->second;
    if (buffer_size < entry.size_bytes) {
        throw std::runtime_error("Buffer too small for file");
    }

    LbaNode node = node_map_.at(entry.file_id);

    NvmeDevice* dev = static_cast<NvmeDevice*>(nvme_device_);
    nvme_host::read_blocks(dev, node.start_lba, node.length, buffer);

    return entry.size_bytes;
}
```

Source: `src/host/nvme_simple_fs.cpp:258-275`

**Usage:**
```cpp
std::vector<std::uint8_t> buffer(4096);
std::size_t bytes_read = fs->read_file("test.bin", buffer.data(), buffer.size());
```

### **58.3.3 Writing at Offset**

The `write_file()` function modifies file data at a specific offset with bounds checking:

```cpp
void write_file(const std::string& filename,
                std::uint64_t offset,
                const void* data,
                std::size_t size_bytes) {
    auto it = file_table_.find(filename);
    if (it == file_table_.end()) {
        throw FileNotFoundError("File not found: " + filename);
    }

    FileEntry& entry = it->second;
    if (offset + size_bytes > entry.size_bytes) {
        throw AccessViolationError("Write exceeds file size");
    }

    LbaNode node = node_map_.at(entry.file_id);

    // Calculate LBA offset
    std::uint64_t lba_offset = offset / superblock_.block_size;
    std::uint64_t byte_offset_in_block = offset % superblock_.block_size;

    // Read-modify-write for unaligned access
    std::uint64_t write_blocks =
        (byte_offset_in_block + size_bytes + superblock_.block_size - 1)
        / superblock_.block_size;

    std::vector<std::uint8_t> temp_buffer(write_blocks * superblock_.block_size);

    NvmeDevice* dev = static_cast<NvmeDevice*>(nvme_device_);

    nvme_host::read_blocks(dev, node.start_lba + lba_offset,
                          write_blocks, temp_buffer.data());

    std::memcpy(temp_buffer.data() + byte_offset_in_block, data, size_bytes);

    nvme_host::write_blocks(dev, node.start_lba + lba_offset,
                           write_blocks, temp_buffer.data());

    entry.modified_time = get_current_timestamp();
    save_metadata();
}
```

Source: `src/host/nvme_simple_fs.cpp:277-314`

**Key Points:**
- Bounds checking prevents writes beyond file size
- Unaligned writes use read-modify-write to preserve surrounding data
- Metadata (modified time) is updated after successful write

**Usage:**
```cpp
std::vector<std::uint8_t> patch(512, 0xCD);
fs->write_file("test.bin", 1024, patch.data(), patch.size());
```

### **58.3.4 Deleting Files**

The `delete_file()` function removes a file and frees its LBA node:

```cpp
bool delete_file(const std::string& filename) {
    auto it = file_table_.find(filename);
    if (it == file_table_.end()) {
        return false;
    }

    std::uint32_t file_id = it->second.file_id;
    LbaNode node = node_map_.at(file_id);

    file_table_.erase(it);
    node_map_.erase(file_id);
    free_space(node);  // Add to free list

    save_metadata();
    return true;
}
```

Source: `src/host/nvme_simple_fs.cpp:316-332`

After deletion, call `garbage_collect()` to merge adjacent free nodes.

---

## **58.4 Node-based I/O (Template and Runtime)**

This section demonstrates the node-based read/write APIs that operate directly on LBA nodes. The filesystem provides both template versions (for compile-time type safety) and runtime versions (for dynamic usage).

### **58.4.1 Why Node-based I/O?**

Node-based I/O allows direct access to file storage regions without filename lookups, which is useful for:
- **Performance**: Avoids repeated filename → node lookups
- **Batch processing**: Process multiple chunks of a file efficiently
- **Type safety**: Template API ensures correct element size at compile time
- **Flexibility**: Runtime API supports dynamic data types

### **58.4.2 Template API (Compile-time Type Safety)**

Template functions provide type-safe access with automatic size calculation:

```cpp
template<typename T>
void read_node_template(const LbaNode& node,
                       std::uint64_t offset_bytes,
                       T* buffer,
                       std::size_t count) {
    std::size_t size_bytes = count * sizeof(T);
    check_bounds(node, offset_bytes, size_bytes);
    read_node(node, offset_bytes, buffer, size_bytes);
}

template<typename T>
void write_node_template(const LbaNode& node,
                        std::uint64_t offset_bytes,
                        const T* data,
                        std::size_t count) {
    std::size_t size_bytes = count * sizeof(T);
    check_bounds(node, offset_bytes, size_bytes);
    write_node(node, offset_bytes, data, size_bytes);
}
```

Source: `src/host/nvme_simple_fs.cpp:392-413`

**Usage:**
```cpp
// Get LBA node for file
LbaNode node = fs->get_file_node("data.bin");

// Type-safe read of float array
std::vector<float> values(256);
fs->read_node_template<float>(node, 0, values.data(), values.size());

// Type-safe write of double array
std::vector<double> results(128);
fs->write_node_template<double>(node, 1024, results.data(), results.size());
```

**Advantages:**
- Compiler calculates `size_bytes = count * sizeof(T)` automatically
- Type mismatch caught at compile time
- No manual size calculations needed
- Better optimization opportunities

### **58.4.3 Runtime API (Dynamic Bounds Checking)**

Runtime functions accept raw pointers and byte counts for maximum flexibility:

```cpp
void read_node(const LbaNode& node,
               std::uint64_t offset_bytes,
               void* buffer,
               std::size_t size_bytes) {
    check_bounds(node, offset_bytes, size_bytes);

    // Calculate LBA range
    std::uint64_t lba_offset = offset_bytes / superblock_.block_size;
    std::uint64_t byte_offset_in_block = offset_bytes % superblock_.block_size;
    std::uint64_t read_blocks =
        (byte_offset_in_block + size_bytes + superblock_.block_size - 1)
        / superblock_.block_size;

    std::vector<std::uint8_t> temp_buffer(read_blocks * superblock_.block_size);

    NvmeDevice* dev = static_cast<NvmeDevice*>(nvme_device_);
    nvme_host::read_blocks(dev, node.start_lba + lba_offset,
                          read_blocks, temp_buffer.data());

    std::memcpy(buffer, temp_buffer.data() + byte_offset_in_block, size_bytes);
}

void write_node(const LbaNode& node,
                std::uint64_t offset_bytes,
                const void* data,
                std::size_t size_bytes) {
    check_bounds(node, offset_bytes, size_bytes);

    // Similar implementation with read-modify-write
    // (see source code for full implementation)
}
```

Source: `src/host/nvme_simple_fs.cpp:437-475`

**Usage:**
```cpp
LbaNode node = fs->get_file_node("binary.dat");

std::vector<std::uint8_t> buffer(1024);
fs->read_node(node, 2048, buffer.data(), buffer.size());

std::vector<std::uint8_t> data(512, 0xFF);
fs->write_node(node, 1024, data.data(), data.size());
```

### **58.4.4 Bounds Checking**

All node-based I/O operations perform bounds checking to prevent access violations:

```cpp
void check_bounds(const LbaNode& node,
                  std::uint64_t offset,
                  std::size_t size) const {
    std::uint64_t node_size_bytes = node.length * superblock_.block_size;

    if (offset + size > node_size_bytes) {
        std::ostringstream oss;
        oss << "Access violation: trying to access " << size
            << " bytes at offset " << offset
            << " in node of size " << node_size_bytes << " bytes";
        throw AccessViolationError(oss.str());
    }
}
```

Source: `src/host/nvme_simple_fs.cpp:211-224`

**Example:**
```cpp
LbaNode node = fs->get_file_node("small.bin");  // 1024 bytes

std::vector<std::uint8_t> buffer(512);

// This will throw AccessViolationError
fs->read_node(node, 2048, buffer.data(), buffer.size());
```

---

## **58.5 Garbage Collection**

This section explains how the filesystem manages fragmentation through garbage collection, which merges adjacent free LBA nodes to create larger contiguous regions.

### **58.5.1 Fragmentation Problem**

After multiple file creations and deletions, the free list may contain many small, non-contiguous nodes:

```
Before GC:
Free list: [Node(LBA 100, len 10), Node(LBA 110, len 20), Node(LBA 200, len 15)]
```

If nodes are adjacent (e.g., Node 1 ends at LBA 110, Node 2 starts at LBA 110), they can be merged into a single larger node.

### **58.5.2 Garbage Collection Algorithm**

The `garbage_collect()` function sorts the free list by start LBA and merges adjacent nodes:

```cpp
std::size_t garbage_collect() {
    // Sort free list by start_lba
    std::sort(free_list_.begin(), free_list_.end(),
              [](const LbaNode& a, const LbaNode& b) {
                  return a.start_lba < b.start_lba;
              });

    // Merge adjacent free nodes
    std::size_t merged_count = 0;
    for (std::size_t i = 0; i + 1 < free_list_.size(); ) {
        if (free_list_[i].end_lba() == free_list_[i+1].start_lba) {
            // Nodes are adjacent, merge them
            free_list_[i].length += free_list_[i+1].length;
            free_list_.erase(free_list_.begin() + i + 1);
            merged_count++;
        } else {
            i++;
        }
    }

    if (merged_count > 0) {
        save_metadata();
    }

    return merged_count;
}
```

Source: `src/host/nvme_simple_fs.cpp:477-501`

**Example:**
```
Before GC:
Free list: [Node(100, 10), Node(110, 20), Node(200, 15)]

After sort:
Free list: [Node(100, 10), Node(110, 20), Node(200, 15)]

After merge:
Free list: [Node(100, 30), Node(200, 15)]  // Merged first two nodes
Merged count: 1
```

**Usage:**
```cpp
fs->save_file("file1.bin", data1, size1);
fs->save_file("file2.bin", data2, size2);
fs->save_file("file3.bin", data3, size3);

fs->delete_file("file2.bin");  // Creates gap in LBA space

std::size_t merged = fs->garbage_collect();  // Merge adjacent free nodes
std::cout << "Merged " << merged << " nodes\n";
```

**When to Run GC:**
- After deleting multiple files
- Before allocating a large file
- Periodically during batch operations
- When allocation fails due to fragmentation

---

## **58.6 C API Wrapper**

This section describes the C-compatible API wrapper, which enables integration with C code, Python bindings (via ctypes/cffi), and other languages through FFI (Foreign Function Interface).

### **58.6.1 Why a C API?**

C++ classes with templates, exceptions, and RAII are not directly callable from C or other languages. A C API provides:

- **Language interoperability**: Callable from C, Python, Rust, Go, etc.
- **ABI stability**: C has a stable ABI across compilers
- **Simple error handling**: Return codes instead of exceptions
- **FFI compatibility**: Works with ctypes, cffi, FFI libraries

### **58.6.2 C API Design**

The C API (defined in `src/common/nvme_simple_fs_c_api.h`) wraps the C++ implementation:

```c
// Opaque handle (hides C++ implementation)
typedef struct nvme_fs_handle nvme_fs_handle_t;

// C-compatible structures
typedef struct {
    uint64_t start_lba;
    uint64_t length;
    uint32_t file_id;
    uint32_t flags;
} nvme_fs_node_t;

typedef struct {
    char     name[256];
    uint32_t file_id;
    uint64_t size_bytes;
    uint64_t created_time;
    uint64_t modified_time;
    uint32_t checksum;
} nvme_fs_file_info_t;

// Filesystem lifecycle
nvme_fs_handle_t* nvme_fs_create(void* nvme_device,
                                 uint64_t start_lba,
                                 uint64_t total_blocks,
                                 uint64_t block_size);
nvme_fs_handle_t* nvme_fs_open(void* nvme_device, uint64_t start_lba);
void nvme_fs_close(nvme_fs_handle_t* fs);

// File operations
uint32_t nvme_fs_save_file(nvme_fs_handle_t* fs, const char* filename,
                           const void* data, size_t size_bytes);
size_t nvme_fs_read_file(nvme_fs_handle_t* fs, const char* filename,
                         void* buffer, size_t buffer_size);
int nvme_fs_write_file(nvme_fs_handle_t* fs, const char* filename,
                       uint64_t offset, const void* data, size_t size_bytes);
int nvme_fs_delete_file(nvme_fs_handle_t* fs, const char* filename);

// Node-based I/O
int nvme_fs_read_node(nvme_fs_handle_t* fs, const nvme_fs_node_t* node,
                      uint64_t offset_bytes, void* buffer, size_t size_bytes);
int nvme_fs_write_node(nvme_fs_handle_t* fs, const nvme_fs_node_t* node,
                       uint64_t offset_bytes, const void* data, size_t size_bytes);

// Error handling
const char* nvme_fs_get_last_error(void);
```

Source: `src/common/nvme_simple_fs_c_api.h`

### **58.6.3 C API Implementation**

The wrapper (in `src/host/nvme_simple_fs_c_api.cpp`) translates C calls to C++ calls:

```cpp
nvme_fs_handle_t* nvme_fs_create(void* nvme_device,
                                 uint64_t start_lba,
                                 uint64_t total_blocks,
                                 uint64_t block_size) {
    try {
        auto fs = nvme_fs::create_filesystem(nvme_device, start_lba,
                                             total_blocks, block_size);
        return reinterpret_cast<nvme_fs_handle_t*>(fs.release());
    } catch (const std::exception& e) {
        set_error(e.what());
        return nullptr;
    }
}

uint32_t nvme_fs_save_file(nvme_fs_handle_t* fs,
                           const char* filename,
                           const void* data,
                           size_t size_bytes) {
    if (!fs || !filename || !data) return 0;

    try {
        auto* filesystem = reinterpret_cast<nvme_fs::NvmeSimpleFilesystem*>(fs);
        return filesystem->save_file(filename, data, size_bytes);
    } catch (const std::exception& e) {
        set_error(e.what());
        return 0;
    }
}

const char* nvme_fs_get_last_error(void) {
    return g_last_error.c_str();
}
```

Source: `src/host/nvme_simple_fs_c_api.cpp:18-69`

**Key Points:**
- Exceptions are caught and converted to error codes + error strings
- Opaque handle hides C++ class implementation
- Thread-local error storage for error messages
- Return codes: 0 = success, negative = error

### **58.6.4 C API Usage Example**

```c
#include "nvme_simple_fs_c_api.h"
#include <stdio.h>

int main() {
    // Create filesystem
    nvme_fs_handle_t* fs = nvme_fs_create(nvme_device, 0, 1000000, 512);
    if (!fs) {
        fprintf(stderr, "Error: %s\n", nvme_fs_get_last_error());
        return 1;
    }

    // Save file
    uint8_t data[2048];
    uint32_t file_id = nvme_fs_save_file(fs, "test.bin", data, sizeof(data));
    if (file_id == 0) {
        fprintf(stderr, "Save failed: %s\n", nvme_fs_get_last_error());
    }

    // Get file info
    nvme_fs_file_info_t info;
    if (nvme_fs_get_file_info(fs, "test.bin", &info) == 0) {
        printf("File: %s, Size: %llu bytes\n", info.name, info.size_bytes);
    }

    // Node-based read
    nvme_fs_node_t node;
    nvme_fs_get_file_node(fs, "test.bin", &node);
    uint8_t buffer[1024];
    nvme_fs_read_node(fs, &node, 512, buffer, sizeof(buffer));

    // Cleanup
    nvme_fs_close(fs);
    return 0;
}
```

### **58.6.5 Python Binding Example (ctypes)**

The C API can be easily wrapped in Python using ctypes:

```python
import ctypes
from ctypes import c_void_p, c_uint64, c_uint32, c_char_p, c_size_t, POINTER

# Load library
libfs = ctypes.CDLL("./lib58_Simple_Filesystem_Layer_lib.so")

# Define C structures
class NvmeFsNode(ctypes.Structure):
    _fields_ = [
        ("start_lba", c_uint64),
        ("length", c_uint64),
        ("file_id", c_uint32),
        ("flags", c_uint32)
    ]

# Define C functions
libfs.nvme_fs_create.argtypes = [c_void_p, c_uint64, c_uint64, c_uint64]
libfs.nvme_fs_create.restype = c_void_p

libfs.nvme_fs_save_file.argtypes = [c_void_p, c_char_p, c_void_p, c_size_t]
libfs.nvme_fs_save_file.restype = c_uint32

# Usage
fs = libfs.nvme_fs_create(nvme_device, 0, 1000000, 512)
data = bytes([0xAB] * 4096)
file_id = libfs.nvme_fs_save_file(fs, b"test.bin", data, len(data))
libfs.nvme_fs_close(fs)
```

---

## **58.7 Testing**

This section describes the comprehensive test suite that validates filesystem functionality, including basic operations, node-based I/O, and the C API wrapper.

### **58.7.1 Test Architecture**

Tests use a software NVMe device to avoid requiring real hardware:

```cpp
class MockNvmeDevice {
public:
    static constexpr std::size_t TOTAL_BLOCKS = 10000;
    static constexpr std::size_t BLOCK_SIZE = 512;

    std::vector<std::uint8_t> storage;

    MockNvmeDevice() : storage(TOTAL_BLOCKS * BLOCK_SIZE, 0) {}

    void read_blocks(std::uint64_t lba, std::uint64_t count, void* buffer) {
        std::size_t offset = lba * BLOCK_SIZE;
        std::size_t size = count * BLOCK_SIZE;
        std::memcpy(buffer, storage.data() + offset, size);
    }

    void write_blocks(std::uint64_t lba, std::uint64_t count, const void* buffer) {
        std::size_t offset = lba * BLOCK_SIZE;
        std::size_t size = count * BLOCK_SIZE;
        std::memcpy(storage.data() + offset, buffer, size);
    }
};
```

Source: `test/unit/host/test_filesystem_basic.cpp:10-35`

The mock device implements the same interface as the real NVMe device from Module 53, allowing tests to run without hardware dependencies.

### **58.7.2 Basic Filesystem Tests**

Tests in `test/unit/host/test_filesystem_basic.cpp` cover core operations:

```cpp
TEST_F(FilesystemBasicTest, SaveAndReadFile) {
    std::vector<std::uint8_t> data(4096);
    for (std::size_t i = 0; i < data.size(); ++i) {
        data[i] = static_cast<std::uint8_t>(i % 256);
    }

    std::uint32_t file_id = fs->save_file("test.bin", data.data(), data.size());
    EXPECT_GT(file_id, 0);

    std::vector<std::uint8_t> read_buffer(data.size());
    std::size_t read_bytes = fs->read_file("test.bin", read_buffer.data(),
                                           read_buffer.size());

    EXPECT_EQ(read_bytes, data.size());
    EXPECT_EQ(read_buffer, data);
}

TEST_F(FilesystemBasicTest, AccessViolation) {
    std::vector<std::uint8_t> data(1024, 0xCC);
    fs->save_file("small.bin", data.data(), data.size());

    std::vector<std::uint8_t> buffer(512);

    // Try to write past end of file (should throw)
    EXPECT_THROW(fs->write_file("small.bin", 1024, buffer.data(), buffer.size()),
                 nvme_fs::AccessViolationError);

    // Try to read past end of file (should throw)
    nvme_fs::LbaNode node = fs->get_file_node("small.bin");
    EXPECT_THROW(fs->read_node(node, 2048, buffer.data(), buffer.size()),
                 nvme_fs::AccessViolationError);
}
```

Source: `test/unit/host/test_filesystem_basic.cpp:60-75, 139-153`

**Test Coverage:**
- Filesystem creation and initialization
- File save, read, write, delete operations
- File metadata retrieval
- Listing files
- Bounds checking and access violations
- Garbage collection
- Node-based I/O (runtime and template)

### **58.7.3 C API Tests**

Tests in `test/unit/host/test_c_api.cpp` validate the C API wrapper:

```cpp
TEST_F(CApiTest, SaveAndReadFile) {
    std::vector<uint8_t> data(2048);
    for (size_t i = 0; i < data.size(); ++i) {
        data[i] = static_cast<uint8_t>(i % 256);
    }

    uint32_t file_id = nvme_fs_save_file(fs, "test.bin", data.data(), data.size());
    EXPECT_GT(file_id, 0);

    std::vector<uint8_t> buffer(2048);
    size_t read_bytes = nvme_fs_read_file(fs, "test.bin", buffer.data(),
                                          buffer.size());

    EXPECT_EQ(read_bytes, data.size());
    EXPECT_EQ(buffer, data);
}

TEST_F(CApiTest, NodeBasedIO) {
    std::vector<uint8_t> data(4096);
    for (size_t i = 0; i < data.size(); ++i) {
        data[i] = static_cast<uint8_t>(i % 256);
    }

    nvme_fs_save_file(fs, "node.bin", data.data(), data.size());

    nvme_fs_node_t node;
    int ret = nvme_fs_get_file_node(fs, "node.bin", &node);
    EXPECT_EQ(ret, 0);

    std::vector<uint8_t> buffer(1024);
    ret = nvme_fs_read_node(fs, &node, 2048, buffer.data(), buffer.size());
    EXPECT_EQ(ret, 0);

    for (size_t i = 0; i < buffer.size(); ++i) {
        EXPECT_EQ(buffer[i], (2048 + i) % 256);
    }
}
```

Source: `test/unit/host/test_c_api.cpp:40-66, 94-118`

### **58.7.4 Running Tests**

```bash
# Build tests
cd build
ninja 58_Simple_Filesystem_Layer_test

# Run all tests
./50.GPU-NVMe_Interaction/58.Simple_Filesystem_Layer/test/58_Simple_Filesystem_Layer_test

# Run specific test
./50.GPU-NVMe_Interaction/58.Simple_Filesystem_Layer/test/58_Simple_Filesystem_Layer_test \
  --gtest_filter=FilesystemBasicTest.SaveAndReadFile

# Run with verbose output
./50.GPU-NVMe_Interaction/58.Simple_Filesystem_Layer/test/58_Simple_Filesystem_Layer_test \
  --gtest_verbose
```

---

## Build & Run

### Prerequisites

- CUDA 13.0 or above
- CMake 3.18+
- Ninja build system
- GoogleTest library
- Module 53 (NVMe VFIO Host Layer)
- Module 54 (CUDA Host Memory)

### Building

```bash
# From project root
mkdir -p build && cd build

# Configure
cmake -G Ninja ..

# Build module 58
ninja 58_Simple_Filesystem_Layer_lib
ninja 58_Simple_Filesystem_Layer_test

# Generate documentation
ninja doxygen_58_Simple_Filesystem_Layer
```

### Running Tests

```bash
# Run all tests
ninja test

# Or run directly
./50.GPU-NVMe_Interaction/58.Simple_Filesystem_Layer/test/58_Simple_Filesystem_Layer_test

# View test results
ctest --test-dir 50.GPU-NVMe_Interaction/58.Simple_Filesystem_Layer/test --verbose
```

### Viewing Documentation

```bash
# Open generated HTML documentation
xdg-open build/50.GPU-NVMe_Interaction/58.Simple_Filesystem_Layer/src/doxygen/html/index.html
```

---

## Summary

### **Key Takeaways**

1. **Simple filesystem design**: Node-based LBA management provides file abstraction over raw NVMe storage
2. **Dual API approach**: Template API for compile-time safety, runtime API for flexibility
3. **Bounds checking**: All read/write operations validate access ranges to prevent corruption
4. **C API wrapper**: Enables language interoperability and FFI bindings
5. **Garbage collection**: Periodic merging of free nodes reduces fragmentation

### **Architecture Highlights**

| Component | Purpose | Key Features |
|-----------|---------|--------------|
| LBA Nodes | Storage allocation | Consecutive blocks, first-fit allocation |
| File Table | Metadata management | Name mapping, timestamps, checksums |
| Superblock | Filesystem metadata | Magic number, version, block counts |
| Free List | Space tracking | Sorted list, merge during GC |
| Template API | Type-safe I/O | Compile-time size calculation |
| Runtime API | Flexible I/O | Dynamic bounds checking |
| C API | Language binding | Error codes, opaque handles |

### **Performance Characteristics**

- **Allocation**: O(n) where n = number of free nodes (first-fit search)
- **File lookup**: O(log n) with std::map (filename → file entry)
- **Read/Write**: O(1) once LBA node is known
- **Garbage collection**: O(n log n) for sorting + O(n) for merging
- **Metadata flush**: O(m) where m = number of files + nodes

### **Common Operations**

```cpp
// Create filesystem
auto fs = nvme_fs::create_filesystem(device, 0, 1000000, 512);

// Save file
fs->save_file("data.bin", data, size);

// Read file
fs->read_file("data.bin", buffer, buffer_size);

// Node-based I/O
auto node = fs->get_file_node("data.bin");
fs->read_node_template<float>(node, 0, values, count);

// Garbage collection
fs->garbage_collect();

// Flush metadata
fs->flush_metadata();
```

### **Common Errors & Solutions**

| Error | Cause | Solution |
|-------|-------|----------|
| OutOfSpaceError | No contiguous region large enough | Run GC, delete files, or expand filesystem |
| FileNotFoundError | File doesn't exist | Check filename, call list_files() |
| AccessViolationError | Read/write out of bounds | Check offset + size <= file size |
| Invalid magic number | Corrupted or unformatted filesystem | Call format() or create new filesystem |

### **Next Steps**

- 📚 Continue to [Part 59: Python and PyTorch Bindings](../59.Python_and_PyTorch_Bindings/README.md)
- 🔧 Integrate filesystem with Module 55+ (GPU memory I/O)
- 📊 Benchmark filesystem performance vs. GDS

### **References**

- [Module 53: NVMe VFIO Host Layer](../53.NVMe_VFIO_Host_Layer/README.md) - Base NVMe I/O layer
- [Module 54: CUDA Host Memory](../54.CUDA_Host_Memory/README.md) - Pinned memory integration
- [NVMe Specification](https://nvmexpress.org/specifications/) - NVMe protocol details
