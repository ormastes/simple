# 🎯 Part 51.2: NVMe Fundamentals

**Goal**: Understand NVMe queue architecture, doorbell mechanisms, data transfer methods (PRP/SGL), and DBC shadow doorbell optimization.

This section covers the core NVMe concepts required for user-space NVMe driver implementation, including queue operations, doorbell registers, and advanced features like DBC.

---

## Quick Navigation

- [51.2.1 NVMe Queue Architecture](#5121-nvme-queue-architecture)
- [51.2.2 Doorbell Mechanisms](#5122-doorbell-mechanisms)
- [51.2.3 Data Transfer: PRP and SGL](#5123-data-transfer-prp-and-sgl)
- [51.2.4 DBC Shadow Doorbell and EventIdx](#5124-dbc-shadow-doorbell-and-eventidx)

---

## **51.2.1 NVMe Queue Architecture**

NVMe uses a queue-based architecture for command submission and completion.

### **Queue Pairs**

Each I/O path consists of two queues:

```
┌─────────────────────────────────────────────────────────────┐
│ Host (CPU/GPU)                                              │
│                                                             │
│  Submission Queue (SQ)          Completion Queue (CQ)       │
│  ┌──────────────┐               ┌──────────────┐            │
│  │ Cmd 0        │               │ Comp 0       │            │
│  │ Cmd 1        │               │ Comp 1       │            │
│  │ Cmd 2        │               │ ...          │            │
│  │ ...          │               └──────────────┘            │
│  └──────────────┘                     ▲                     │
│        │                              │                     │
└────────┼──────────────────────────────┼─────────────────────┘
         │                              │
         ▼ (Host rings doorbell)        │ (NVMe writes completion)
┌─────────────────────────────────────────────────────────────┐
│ NVMe Controller                                             │
│  - Reads SQ entries via DMA                                 │
│  - Processes commands                                       │
│  - Writes CQ entries via DMA                                │
└─────────────────────────────────────────────────────────────┘
```

**Submission Queue (SQ):**
- Host writes commands here
- Ring-buffer structure (circular queue)
- Host updates tail pointer via doorbell
- NVMe reads entries via DMA

**Completion Queue (CQ):**
- NVMe writes completions here
- One CQ can serve multiple SQs
- Host polls or uses interrupts
- Host updates head pointer via doorbell

### **Admin vs I/O Queues**

| Queue Type | Purpose | Always Present | QID |
|------------|---------|----------------|-----|
| **Admin Queue** | Controller configuration, namespace management | Yes (mandatory) | 0 (ASQ/ACQ) |
| **I/O Queues** | Read/Write data operations | Optional (created on demand) | 1-65535 |

**Admin Queue operations:**
- Identify controller
- Create/Delete I/O queues
- Set features (DBC, interrupt coalescing)
- Namespace management

**I/O Queue operations:**
- Read/Write commands
- Flush, Compare
- Dataset Management

### **Queue Lifecycle**

```
1. Controller Reset
   ↓
2. Enable Controller (CC.EN=1)
   ↓
3. Wait for CSTS.RDY=1
   ↓
4. Admin Queue is ready (ASQ/ACQ programmed during init)
   ↓
5. Create I/O Completion Queue (Admin Command: Create I/O CQ)
   ↓
6. Create I/O Submission Queue (Admin Command: Create I/O SQ)
   ↓
7. I/O Queue ready for commands
```

---

## **51.2.2 Doorbell Mechanisms**

Doorbells are MMIO registers used to notify the NVMe controller of queue updates.

### **MMIO Doorbell Registers**

**Location**: NVMe BAR0 (Base Address Register 0)

```
BAR0 Memory Map:
┌────────────────────────────────────────┐
│ 0x0000: Controller Capabilities (CAP)  │
│ 0x0008: Version (VS)                   │
│ 0x0014: Controller Configuration (CC)  │
│ 0x001C: Controller Status (CSTS)       │
│ ...                                    │
├────────────────────────────────────────┤
│ 0x1000: Admin SQ Tail Doorbell         │ ← Doorbell base
│ 0x1004: Admin CQ Head Doorbell         │
│ 0x1000 + stride: I/O SQ1 Tail          │
│ 0x1004 + stride: I/O CQ1 Head          │
│ ...                                    │
└────────────────────────────────────────┘
```

**Doorbell stride calculation:**

```c
// Read stride from CAP register (bits 35:32)
uint64_t cap = *(volatile uint64_t*)(bar0 + 0x00);
uint32_t dstrd = (cap >> 32) & 0xF;  // Doorbell stride (power of 2)
uint32_t stride_bytes = 4 << dstrd;  // Stride in bytes

// Calculate doorbell addresses
volatile uint32_t* sq_doorbell = (uint32_t*)(bar0 + 0x1000 + (2 * qid) * stride_bytes);
volatile uint32_t* cq_doorbell = (uint32_t*)(bar0 + 0x1000 + (2 * qid + 1) * stride_bytes);
```

### **GPU Cannot Access MMIO Doorbells**

**Critical limitation**: GPU kernels cannot write to BAR0 MMIO addresses.

```
Traditional MMIO:
GPU ──X──> BAR0 MMIO Doorbell (❌ GPU cannot access)
      PCIe P2P limitation
```

**Why**: MMIO addresses are not mapped through IOVA, and GPU cannot directly access PCIe MMIO regions.

**Workarounds**:
1. CPU writes doorbell (requires GPU→CPU synchronization)
2. DBC Shadow Doorbell (Module 55.2)
3. Host daemon polling (Module 55.3)

---

## **51.2.3 Data Transfer: PRP and SGL**

NVMe uses PRP (Physical Region Pages) or SGL (Scatter-Gather Lists) to describe data buffer locations.

### **PRP (Physical Region Page)**

Despite the name, with IOMMU enabled, PRP entries contain **IOVAs**, not physical addresses.

**PRP Entry Types:**

**1. Single page (≤4KB):**
```
prp1 = iova + offset;
prp2 = 0;  // Not used
```

**2. Two pages (4KB < size ≤ 8KB):**
```
prp1 = iova_page0 + offset;
prp2 = iova_page1;  // Must be page-aligned
```

**3. PRP List (>8KB):**
```
prp1 = data_iova_page0 + offset;
prp2 = prp_list_iova;  // Points to list in host memory

PRP List (in host memory):
  [0] = iova_page1 (page-aligned)
  [1] = iova_page2 (page-aligned)
  [2] = iova_page3 (page-aligned)
  ...
```

**PRP Alignment Rules:**

```c
// ✅ CORRECT
cmd.prp1 = gpu_iova + 512;          // OK: offset allowed
cmd.prp2 = gpu_iova + 4096;         // OK: page-aligned

// ❌ WRONG
cmd.prp2 = gpu_iova + 4096 + 100;   // ERROR: not page-aligned!

// PRP List entries must be page-aligned
prp_list[0] = gpu_iova + 8192;      // OK: multiple of 4096
prp_list[1] = gpu_iova + 12288;     // OK: multiple of 4096
```

### **SGL (Scatter-Gather List)**

More flexible than PRP, supports non-contiguous segments.

```c
struct nvme_sgl_desc {
    uint64_t addr;      // IOVA of segment
    uint32_t length;    // Segment length
    uint8_t  rsvd[3];
    uint8_t  type;      // SGL descriptor type
};
```

**When to use SGL:**
- ✅ Non-contiguous GPU memory
- ✅ Complex scatter-gather patterns
- ⚠️ Not all NVMe controllers support SGL

---

## **51.2.4 DBC Shadow Doorbell and EventIdx**

DBC (Doorbell Buffer Config) is an NVMe 1.3+ feature that enables memory-mapped doorbell updates instead of MMIO.

### **DBC Shadow Doorbell**

**Concept**: Replace MMIO doorbell writes with writes to host memory buffer.

```
DBC Shadow Doorbell:
GPU ──✓──> Shadow Buffer (pinned host memory, IOVA-mapped)
                ↓
           NVMe Controller polls shadow buffer via PCIe DMA ✅
```

**Memory location**: Host system DRAM (allocated with `dma_alloc_coherent()`)

**Buffer layout:**

```
Shadow Doorbell Buffer (Host Memory):
┌────────────────────────────────────────┐
│ Offset 0x00: SQ0 Tail (Admin queue)    │  4 bytes
│ Offset 0x04: CQ0 Head (Admin queue)    │  4 bytes
│ Offset 0x08: SQ1 Tail (I/O queue 1)    │  4 bytes
│ Offset 0x0C: CQ1 Head (I/O queue 1)    │  4 bytes
│ ...                                    │
└────────────────────────────────────────┘

Index: SQ doorbell = 2 × queue_id
       CQ doorbell = 2 × queue_id + 1
```

**Latency comparison:**

| Method | Latency | Notes | Source |
|--------|---------|-------|--------|
| Direct MMIO doorbell | ~200-500ns | Fastest, but GPU cannot access | [1] Intel NVMe spec |
| DBC shadow (hardware polling) | ~5-10μs | NVMe polls host memory via DMA | [2] See Module 55.2 |
| Host daemon polling | ~22-100μs | CPU daemon polls + writes MMIO | [3] Module 55.3 benchmarks |

### **EventIdx Buffer**

EventIdx is an optional optimization that reduces redundant shadow doorbell writes.

**Direction**:
- Shadow Doorbell: Host/GPU → NVMe (tells NVMe where to read)
- EventIdx: NVMe → Host/GPU (tells host where NVMe has processed)

**How it works:**

| Time | Without EventIdx (Baseline) | With EventIdx (threshold=2) |
|------|----------------------------|----------------------------|
| **0μs** | GPU: Submit cmd 1<br>**→ Write Shadow DB = 1** | GPU: Submit cmd 1<br>Read EventIdx=0, Diff=1≤2<br>**→ SKIP shadow write** |
| **0.5μs** | GPU: Submit cmd 2<br>**→ Write Shadow DB = 2** | GPU: Submit cmd 2<br>Read EventIdx=0, Diff=2≤2<br>**→ SKIP shadow write** |
| **1.0μs** | GPU: Submit cmd 3<br>**→ Write Shadow DB = 3** | GPU: Submit cmd 3<br>Read EventIdx=0, Diff=3>2<br>**→ Write Shadow DB = 3** ✅ |
| **5μs** | NVMe: Poll Shadow DB=3<br>Process cmds 1-3 | NVMe: Poll Shadow DB=3<br>Process cmds 1-3<br>**→ Write EventIdx = 3** |

**Result**: 57% reduction in shadow doorbell writes for burst workloads.

**When EventIdx helps:**
- ✅ High queue depth (many outstanding commands)
- ✅ Fast command submission rate (GPU submitting rapidly)
- ✅ VM environments (reduces VM exits in QEMU/KVM)

**When EventIdx doesn't help:**
- ❌ Low queue depth (1-2 commands at a time)
- ❌ Slow command rate (human-initiated I/O)

---

## **Summary**

This section covered NVMe fundamentals:

1. **Queue Architecture**: SQ/CQ pairs, Admin vs I/O queues, lifecycle
2. **Doorbell Mechanisms**: MMIO registers, stride calculation, GPU limitations
3. **Data Transfer**: PRP/SGL for describing buffer locations, alignment rules
4. **DBC Shadow Doorbell**: Memory-mapped doorbell alternative, EventIdx optimization

**Key Takeaways:**
- NVMe uses queue pairs (SQ/CQ) for asynchronous command/completion
- Doorbells notify controller of updates (MMIO or DBC shadow)
- PRP/SGL entries must contain **IOVA** (not CPU-VA or GPU-VA)
- DBC enables GPU to update doorbells without MMIO access

**Next**: [Part 51.3: System Setup](../51.3.System_Setup/README.md) - Learn how to configure VFIO, enable IOMMU, and set up GPU memory integration.
