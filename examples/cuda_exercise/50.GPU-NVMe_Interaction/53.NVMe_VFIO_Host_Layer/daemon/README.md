# Host DBC Daemon - Module 56

This directory contains the host DBC daemon implementations for Module 56 (GPU-initiated NVMe I/O with shadow doorbells).

## Overview

The host DBC daemon implements the Module 55.3 doorbell approach:
- GPU writes shadow doorbell buffer in **host memory** (pinned, GPU-accessible via PCIe)
- Daemon polls shadow buffer in host memory (no PCIe overhead for daemon)
- Daemon rings actual NVMe MMIO doorbells on GPU's behalf
- Works on all hardware (no DBC support required)

## Daemon Performance Modes

Two daemon implementations are provided with different performance/CPU usage trade-offs:

### Standard Daemon (`host_dbc_daemon`)

**Features**:
- Polling interval: 10µs (configurable via `--poll-interval`)
- Low CPU usage: 1-5%
- Uses `std::this_thread::sleep_for()` for polling

**Performance**:
- Latency: 12-50µs for 4KB reads
- Throughput: 20-80K IOPS
- Best for: General purpose, shared CPU workloads

**Usage**:
```bash
./host_dbc_daemon \
    --device /dev/nvme0 \
    --qid 1 \
    --shadow 0x7f8a40000000 \
    --poll-interval 10
```

**Configuration Options**:
```
--device PATH       NVMe device path (default: /dev/nvme0)
--qid NUM           Queue ID to monitor (default: 1)
--shadow PTR        Shadow doorbell buffer address (hex)
--sq-depth NUM      SQ depth (default: 64)
--cq-depth NUM      CQ depth (default: 64)
--poll-interval US  Polling interval in microseconds (default: 10)
```

### Realtime Daemon (`host_dbc_daemon_realtime`)

**Features**:
- Busy-wait polling (no sleep)
- Real-time scheduling (SCHED_FIFO)
- CPU affinity pinning to isolated core
- Memory locking (no page faults)

**Performance**:
- Latency: 4-8µs for 4KB reads (3-6x improvement)
- Throughput: 125-250K IOPS
- CPU usage: 100% on one isolated core
- Best for: Ultra-low latency, dedicated I/O workloads

**Requirements**:
1. **Root privileges** (for SCHED_FIFO real-time scheduling)
2. **Isolated CPU core** (via `isolcpus` kernel parameter)
3. **Dedicated core** (will use 100% CPU)

**Setup**:
```bash
# Run setup script to configure system
sudo ./scripts/setup_realtime_daemon.sh 7

# This will:
# - Check for isolated CPU cores
# - Configure real-time limits
# - Add user to 'realtime' group
# - Optionally update GRUB for CPU isolation

# Reboot if GRUB was updated
sudo reboot
```

**Usage**:
```bash
sudo ./host_dbc_daemon_realtime \
    --device /dev/nvme0 \
    --qid 1 \
    --shadow 0x7f8a40000000 \
    --cpu 7 \
    --priority 90
```

**Configuration Options**:
```
--device PATH       NVMe device path (default: /dev/nvme0)
--qid NUM           Queue ID to monitor (default: 1)
--shadow PTR        Shadow doorbell buffer address (hex)
--sq-depth NUM      SQ depth (default: 64)
--cq-depth NUM      CQ depth (default: 64)
--cpu CORE          CPU core to pin to (default: 7)
--priority NUM      Real-time priority 1-99 (default: 90)
```

## Performance Comparison

| Daemon Type | Latency (4KB read) | CPU Usage | Requires Root | Use Case |
|-------------|-------------------|-----------|---------------|----------|
| **Standard (10µs poll)** | 12-50µs | 1-5% | No | General purpose |
| **Standard (1µs poll)** | 4-10µs | 10-20% | No | Latency-sensitive |
| **Realtime (busy-wait)** | 4-8µs | 100% (1 core) | Yes | Ultra-low latency |
| **Direct PCIe** (impossible) | ~2µs | 0% | N/A | Theoretical limit |

**Key Insight**: Realtime daemon approaches direct PCIe performance while working on all hardware.

## Architecture

### Shadow Doorbell Buffer Layout

```
Host Memory (pinned, GPU-accessible):
┌─────────┬─────────┬─────────┬─────────┬─────────┬─────────┐
│  SQ 0   │  CQ 0   │  SQ 1   │  CQ 1   │  SQ 2   │  CQ 2   │ ...
└─────────┴─────────┴─────────┴─────────┴─────────┴─────────┘
   [0]       [1]       [2]       [3]       [4]       [5]

Each entry: 32-bit unsigned integer
SQ/CQ pair for queue N: indices [2N] and [2N+1]
```

### Daemon Operation Flow

**GPU Side** (CUDA kernel):
```cuda
// GPU writes shadow doorbell (host memory accessible via PCIe)
shadow_doorbells[2 * qid] = new_sq_tail;
__threadfence_system();  // Ensure write visible to host
```

**Daemon Side** (host CPU):
```cpp
// Daemon polls shadow doorbell (local host memory read, no PCIe)
uint32_t current = shadow_doorbells[2 * qid];

if (current != last_value) {
    // Ring actual NVMe MMIO doorbell
    *nvme_sq_doorbell = current % sq_depth;
    __sync_synchronize();
}
```

### Latency Breakdown

**Standard Daemon (10µs polling)**:
```
GPU write shadow DB:     2-5µs   (PCIe write to host memory)
Daemon wakeup:          0-10µs   (depends on polling interval)
Daemon read shadow:      <1µs    (host memory read)
Daemon MMIO write:       ~2µs    (BAR0 write)
─────────────────────────────────
Total:                 4-18µs    (best case: daemon polls immediately)
                      12-50µs    (average: daemon polls within interval)
```

**Realtime Daemon (busy-wait)**:
```
GPU write shadow DB:     2-5µs   (PCIe write to host memory)
Daemon detect:           <1µs    (busy-wait, immediate detection)
Daemon MMIO write:       ~2µs    (BAR0 write)
─────────────────────────────────
Total:                  4-8µs    (consistent, low variance)
```

## Why Daemon Instead of Direct PCIe?

**Problem**: GPU cannot directly access NVMe doorbell registers because:
1. **Physical addressing limits**: AMD GFX8 GPUs limited to addresses below 2⁴⁰
2. **System topology**: Requires same PCIe root complex and BIOS support
3. **Linux kernel limitations**: P2P framework doesn't support doorbell registers

**Solution**: Daemon acts as proxy:
- GPU writes to host memory (always accessible via PCIe)
- Daemon polls host memory (no PCIe overhead)
- Daemon writes MMIO doorbells (has BAR access)

## Memory Location: Host Memory (Not GPU VRAM)

**Critical**: Shadow doorbell buffer is in **host system memory** (pinned, GPU-accessible), NOT GPU VRAM.

**Why host memory?**
1. **Future DBC compatibility**: Real DBC (55.2) requires host memory (NVMe spec)
2. **Daemon access**: Host daemon can poll host memory without PCIe overhead
3. **Spec compliance**: Matches NVMe 1.3+ DBC specification layout
4. **Easy migration**: When upgrading to DBC hardware, only remove daemon

## Integration with Module 56

The daemon is designed to work with Module 56's GPU-initiated I/O:

```cpp
// 1. Initialize doorbell mode (creates shadow buffer in host memory)
DoorbellMode mode = HOST_DBC_DAEMON;
nvme_doorbell_mode_init(mode, &shadow_buffer_ptr);

// 2. Start daemon with shadow buffer address
// Get address from nvme_doorbell_mode_init()
printf("Shadow buffer: %p\n", shadow_buffer_ptr);

// 3. Launch daemon (separate process)
// Standard:
./host_dbc_daemon --shadow <addr> --qid 1

// Or realtime:
sudo ./host_dbc_daemon_realtime --shadow <addr> --qid 1 --cpu 7

// 4. GPU kernels write shadow doorbell
gpu_submit_io_kernel<<<...>>>(shadow_buffer_ptr, ...);

// 5. Daemon automatically rings NVMe doorbells
```

## Building

Daemons are built automatically with Module 56:

```bash
cd 56.GPU_Queue_GPU_Buffer
mkdir -p build && cd build
cmake .. -G Ninja
ninja host_dbc_daemon              # Standard daemon
ninja host_dbc_daemon_realtime     # Realtime daemon
```

Executables location:
```
build/daemon/host_dbc_daemon
build/daemon/host_dbc_daemon_realtime
```

## Testing

### Test Standard Daemon

```bash
# Build test
ninja test_56_host_dbc_daemon_mode

# Run integration test (starts daemon automatically)
./test/integration/test_host_dbc_daemon_mode

# Or manually:
./daemon/host_dbc_daemon --shadow <addr> --qid 1 &
DAEMON_PID=$!

# Run GPU I/O test
./test/integration/test_4kb_read

# Stop daemon
kill $DAEMON_PID
```

### Test Realtime Daemon

```bash
# Setup system (one-time)
sudo ./scripts/setup_realtime_daemon.sh 7
sudo reboot

# Run realtime daemon
sudo ./daemon/host_dbc_daemon_realtime \
    --shadow <addr> --qid 1 --cpu 7 --priority 90 &

# Run latency-sensitive benchmark
./test/integration/test_4kb_read_latency

# Observe latency improvement (12-50µs → 4-8µs)
```

### Benchmark Comparison

```bash
# Compare daemon modes
./test/performance/benchmark_daemon_modes.sh

# Expected output:
# Standard (10µs):  Avg latency: 25µs, IOPS: 40K
# Standard (1µs):   Avg latency: 7µs,  IOPS: 140K
# Realtime:         Avg latency: 6µs,  IOPS: 165K
```

## Troubleshooting

### Realtime Daemon Issues

**"Failed to set SCHED_FIFO"**:
- Cause: Not running as root
- Solution: Run with `sudo`

**"CPU X may not be isolated"**:
- Cause: CPU not isolated via kernel parameter
- Solution: Add `isolcpus=X` to GRUB, reboot

**"Failed to lock memory"**:
- Cause: Insufficient memlock limits
- Solution: Run `sudo ./scripts/setup_realtime_daemon.sh`

### Performance Issues

**High latency despite realtime daemon**:
- Check CPU isolation: `cat /sys/devices/system/cpu/isolated`
- Check daemon CPU usage: `top -p $(pidof host_dbc_daemon_realtime)`
- Should show 100% CPU on isolated core

**CPU usage not 100%**:
- Daemon may be sleeping (wrong binary)
- Verify running `host_dbc_daemon_realtime`, not `host_dbc_daemon`

## References

- NVMe Specification 1.4: Section 7.13 (Doorbell Buffer Config)
- Module 55.1: Host Daemon Doorbell (reads sq_tail from GPU memory)
- Module 55.2: DBC Shadow Doorbell (real DBC, hardware support)
- Module 55.3: Host DBC Daemon (software DBC with daemon)
- DAEMON_PERFORMANCE_ANALYSIS.md: Detailed performance analysis

## See Also

- `../include/nvme_doorbell_mode.h` - Doorbell mode API
- `../src/host/doorbell_mode.cpp` - Doorbell mode implementation
- `../test/integration/test_host_dbc_daemon_mode.cu` - Integration test
- `DAEMON_PERFORMANCE_ANALYSIS.md` - Performance optimization analysis
