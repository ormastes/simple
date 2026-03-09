# Doorbell Daemon - Unified In-Process Design

## Overview

The doorbell daemon is an **in-process thread** that monitors changes and rings NVMe MMIO doorbells. It supports both host-initiated and GPU-initiated I/O without requiring sudo or separate processes.

**Class**: `DoorbellDaemon` (in `src/common/doorbell/doorbell_daemon.h`)

---

## Two Operating Modes

### Mode 1: Queue Tail Monitoring (Host-Initiated)

**Use Case:** Host builds NVMe commands, daemon rings doorbells

```cpp
#include "common/doorbell/doorbell_daemon.h"

Queue* iosq = create_io_queue();

// Create daemon monitoring queue tail
DoorbellDaemon daemon(iosq, 10us);
daemon.start();

// Host builds commands
nvme_submit_read(iosq, ...);  // Increments tail

// Daemon automatically rings doorbell
```

**Data Flow:**
```
Host CPU → Writes NVMe command to SQ
Host CPU → Increments iosq->tail
Daemon Thread → Polls iosq->tail
Daemon Thread → Rings MMIO doorbell
```

---

### Mode 2: Shadow Buffer Monitoring (GPU-Initiated)

**Use Case:** GPU builds NVMe commands, writes shadow buffer, daemon mirrors to MMIO

```cpp
#include "common/doorbell/doorbell_daemon.h"
#include "common/doorbell/dbc_setup.h"

// Allocate shadow buffer (host RAM)
ShadowDoorbellBuffer* shadow = allocate_shadow_doorbell_buffer(1);

// Create daemon monitoring shadow buffer
DoorbellDaemon daemon(iosq, shadow, /*qid=*/1, 10us);
daemon.start();

// GPU kernel writes shadow buffer
gpu_submit_io<<<...>>>(shadow->gpu_ptr, ...);

// Daemon automatically rings doorbell
```

**Data Flow:**
```
GPU Kernel → Writes shadow_buffer[qid] (host memory)
Daemon Thread → Polls shadow_buffer[qid]
Daemon Thread → Rings MMIO doorbell
```

---

## Why No Script Needed

### Security: No Sudo Required

The daemon runs **in the same process** as the test, inheriting VFIO access:

```cpp
// Test process (user mode, no sudo needed):
int vfio_fd = open("/dev/vfio/123", O_RDWR);  // User in 'vfio' group

// Map NVMe BAR0 (includes doorbell registers)
void* bar0 = mmap(NULL, bar0_size, PROT_READ | PROT_WRITE,
                  MAP_SHARED, vfio_fd, bar0_offset);

// Create queue with doorbell pointers
Queue* iosq = create_queue(...);
iosq->sq_doorbell = (uint32_t*)(bar0 + doorbell_offset);

// Create daemon (inherits VFIO access)
DoorbellDaemon daemon(iosq, ...);
daemon.start();  // No sudo!
```

**Benefits:**
- ✅ **No privilege escalation** - runs with same user as test
- ✅ **VFIO isolation** - IOMMU protection, not dangerous `/dev/mem`
- ✅ **Simple lifecycle** - automatic cleanup when test ends
- ✅ **No IPC overhead** - same memory space

---

## Implementation Details

### File: `src/common/doorbell/doorbell_daemon.h`

```cpp
namespace nvme {

class DoorbellDaemon {
public:
    // Mode 1: Monitor Queue tail (host-initiated)
    DoorbellDaemon(Queue* iosq,
                   std::chrono::microseconds poll_interval = 10us);

    // Mode 2: Monitor shadow doorbell buffer (GPU-initiated)
    DoorbellDaemon(Queue* iosq,
                   ShadowDoorbellBuffer* shadow_buffer,
                   uint16_t qid,
                   std::chrono::microseconds poll_interval = 10us);

    void start();   // Spawns thread
    void stop();    // Stops and joins thread
    bool is_running() const;
    uint64_t ring_count() const;  // Statistics
};

}  // namespace nvme
```

### Thread Lifecycle

```
Test Process
├── Main Thread
│   ├── Open VFIO (/dev/vfio/*)
│   ├── Map BAR0 (doorbell registers)
│   ├── Create DoorbellDaemon object
│   └── daemon.start()
├── Daemon Thread (spawned)
│   ├── Poll for changes (tail or shadow buffer)
│   ├── Ring MMIO doorbell when changed
│   └── Loop until stopped
└── Main Thread
    ├── Submit I/O operations
    ├── Wait for completions
    └── daemon.stop() (automatic in destructor)
```

---

## Comparison: Old vs New Design

| Aspect | Old (Standalone Process) | New (In-Process Thread) |
|--------|--------------------------|-------------------------|
| **Binary** | Separate `host_dbc_daemon` | Part of test binary |
| **Sudo** | ✅ Required | ❌ Not needed |
| **Launch** | Shell script | `daemon.start()` |
| **Security** | ❌ Entire daemon as root | ✅ Same privileges as test |
| **MMIO Access** | `/dev/mem` (dangerous) | VFIO (safe, IOMMU protected) |
| **IPC** | Shadow buffer address passing | Shared memory space |
| **Lifecycle** | Manual start/stop script | Automatic (RAII) |
| **Status** | ⚠️ Deprecated | ✅ Current design |

---

## Prerequisites

1. **VFIO setup complete**: Device bound to vfio-pci
2. **User in vfio group**: Access to `/dev/vfio/*`
3. **Shadow buffer allocated** (Mode 2 only): See `dbc_shadow_buffer_task.md`

---

## Example: Mode 5 GPU-Initiated I/O

```cpp
#include "common/doorbell/doorbell_daemon.h"
#include "common/doorbell/dbc_setup.h"

// 1. Setup (no sudo)
int vfio_fd = open("/dev/vfio/123", O_RDWR);
void* bar0 = mmap(..., vfio_fd, ...);
Queue* iosq = create_queue_with_vfio(vfio_fd, bar0);

// 2. Allocate shadow buffer (host RAM)
ShadowDoorbellBuffer* shadow = allocate_shadow_doorbell_buffer(1);

// 3. Create and start daemon
DoorbellDaemon daemon(iosq, shadow, /*qid=*/1, 10us);
daemon.start();  // Spawns monitoring thread

// 4. Launch GPU kernel
gpu_submit_io<<<...>>>(shadow->gpu_ptr, iosq_gpu, ...);

// 5. Wait for completion
wait_for_io_completion(iosq);

// 6. Cleanup (automatic)
daemon.stop();
free_shadow_doorbell_buffer(shadow);
```

**Result:** No sudo. No scripts. Just works.

---

## Migration from Standalone Daemon

### Old (Deprecated):
```bash
# Required sudo
sudo SHADOW_HEX=0x7f... ./host_dbc_daemon_task.sh standard /dev/nvme0 1 &
DAEMON_PID=$!
./test_mode5
sudo kill $DAEMON_PID
```

### New (Current):
```cpp
// No sudo needed - all in test code
ShadowDoorbellBuffer* shadow = allocate_shadow_doorbell_buffer(1);
DoorbellDaemon daemon(iosq, shadow, qid, 10us);
daemon.start();
// ... test runs ...
daemon.stop();  // or automatic in destructor
```

---

## References

- **Class Definition:** `src/common/doorbell/doorbell_daemon.h`
- **Shadow Buffer:** `src/common/doorbell/dbc_setup.h`
- **Design Document:** `daemon/UNIFIED_DAEMON_DESIGN.md`
- **Test Example:** `test/system_test/test_mode5_gpu_initiated.cpp`
