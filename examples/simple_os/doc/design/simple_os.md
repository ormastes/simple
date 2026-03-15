# Simple OS - Architecture Design

**Version:** 0.1.0
**Status:** Draft
**Last Updated:** 2026-03-15

---

## 1. System Overview

Simple OS is structured as a minimal microkernel with the following layers:

```
+----------------------------------------------------------+
|  User Applications                                       |
+----------------------------------------------------------+
|  System Servers (VFS, Net, Device Drivers, Init)         |
+----------------------------------------------------------+
|  libsimple_os  (user-space runtime, IPC stubs, syscall) |
+----------------------------------------------------------+
|  ~~~~~~~~~~~~~~~ System Call Boundary ~~~~~~~~~~~~~~~~~~  |
+----------------------------------------------------------+
|  Kernel Core                                             |
|  +----------+  +-----+  +---------+  +---------------+  |
|  | Cap/CSpace|  | IPC |  |Scheduler|  | Memory (Retype)|  |
|  +----------+  +-----+  +---------+  +---------------+  |
|  +--------------------------------------------------+   |
|  | Architecture HAL (x86 / ARM / RISC-V)            |   |
|  +--------------------------------------------------+   |
+----------------------------------------------------------+
|  Hardware                                                |
+----------------------------------------------------------+
```

### 1.1 Design Principles

1. **Minimality:** Only mechanisms in the kernel, policies in user space
2. **Capability discipline:** No ambient authority -- every access requires a capability
3. **No kernel allocation:** All memory comes from user-provided Untyped via Retype
4. **Bounded execution:** Every kernel operation has bounded WCET
5. **Architecture independence:** Kernel core has zero architecture-specific code

### 1.2 Source Layout

```
simple_os/
    build.sdn                  # Build configuration
    kernel/
        core/
            boot.spl           # Kernel entry, initialization
            syscall.spl         # System call dispatch table
            capability.spl      # CapTable, CapSlot, CapRights
            capability_types.spl # CapType enum
            cspace.spl          # CSpace radix tree
            ipc.spl             # IPC buffer, message passing
            endpoint.spl        # Endpoint object
            notification.spl    # Notification object
            scheduler.spl       # Priority scheduler + MCS
            tcb.spl             # Thread control block
            sched_context.spl   # MCS budget/period
        mm/
            untyped.spl         # Untyped memory management
            retype.spl          # Retype operation
            frame_alloc.spl     # Bitmap frame allocator
            vspace.spl          # Virtual address space
        lib/
            bitmap.spl          # Bitmap data structure
            linked_list.spl     # Intrusive linked list
            ring_buffer.spl     # Lock-free ring buffer
    arch/
        x86/
            boot_asm.spl        # Multiboot header, GDT, IDT
            interrupt.spl       # x86 interrupt handling
            mmu.spl             # x86 page table manipulation
            io.spl              # Port I/O
            serial.spl          # Serial port driver (debug)
            timer.spl           # PIT/APIC timer
            context_switch.spl  # Register save/restore
            linker.ld           # Linker script
        arm/
            boot_asm.spl        # ARM boot stub
            interrupt.spl       # GIC interrupt controller
            mmu.spl             # ARM page tables
            serial.spl          # UART driver
            timer.spl           # ARM generic timer
            context_switch.spl  # Register save/restore
        riscv/
            boot_asm.spl        # RISC-V boot stub
            interrupt.spl       # PLIC/CLINT
            mmu.spl             # Sv32 page tables
            serial.spl          # UART driver
            timer.spl           # mtime/mtimecmp
            context_switch.spl  # Register save/restore
    user/
        init.spl               # Initial task (root server)
        libsimple_os.spl       # User-space runtime library
    test/
        unit/kernel/           # Unit tests (hosted mode)
        integration/           # QEMU integration tests
        qemu/                  # QEMU launch scripts
```

---

## 2. Kernel Object Model

All kernel-managed resources are represented as typed objects. Objects are accessed exclusively through capabilities.

### 2.1 Object Types (Tagged Union)

```
enum KernelObject:
    Untyped(region: MemRegion)
    Endpoint(ep: EndpointData)
    Notification(ntfn: NotificationData)
    CNode(slots: List<CapSlot>, guard: Int, guard_bits: Int)
    TCB(thread: ThreadData)
    SchedContext(budget: Int, period: Int, remaining: Int)
    Frame(paddr: Int, size: Int, mapped: Bool)
    PageTable(entries: List<PageTableEntry>)
    IRQHandler(irq: Int, notification: Option<CapSlot>)
    IOPort(base: Int, size: Int)            # x86 only
    VSpace(root_pt: PageTable)
```

### 2.2 Object Lifecycle

1. **Creation:** Retype from UntypedMemory -- carves out a region and initializes the object
2. **Use:** Operations via system calls that take a capability argument
3. **Destruction:** Revoke on the parent UntypedMemory -- recursively destroys all children

All objects are kernel-managed. User space never directly touches kernel data structures.

---

## 3. CSpace Design

### 3.1 Radix Tree Structure

The CSpace is a tree of CNodes. Each CNode contains 2^n capability slots (where n is the CNode's radix/size bits).

```
CSpace Lookup:
    cap_ptr = [guard_1 | index_1 | guard_2 | index_2 | ...]

    Level 0: Root CNode (in TCB)
        - Match guard_1, extract index_1
        - Slot[index_1] points to next CNode
    Level 1: Intermediate CNode
        - Match guard_2, extract index_2
        - Slot[index_2] is the resolved capability
```

### 3.2 CNode Structure

```
struct CNode:
    val slots: List<CapSlot>    # Power-of-2 sized
    val guard: Int              # Guard value for this node
    val guard_bits: Int         # Number of guard bits
    val radix_bits: Int         # log2(num_slots)
```

### 3.3 CapSlot Structure

```
struct CapSlot:
    val type_tag: CapType       # Object type (8 bits)
    val rights: CapRights       # Access rights (8 bits)
    val object_ptr: Int         # Pointer to kernel object (48 bits)
    val badge: Int              # Badge value for IPC identification
    var mdb_next: Option<CapSlot>   # Mapping database: next derived cap
    var mdb_prev: Option<CapSlot>   # Mapping database: prev derived cap
```

### 3.4 Capability Derivation Tree (MDB)

The Mapping DataBase (MDB) tracks the derivation hierarchy of capabilities as a doubly-linked list. This enables transitive revocation: revoking a capability also revokes all capabilities derived from it.

```
Original (Untyped) --> Derived (Endpoint) --> Minted (Endpoint, reduced rights)
     |                       |
     mdb_next -->       mdb_next -->  nil
```

---

## 4. IPC Model

### 4.1 Synchronous Rendezvous

IPC uses the L4 rendezvous model: the sender and receiver must both be ready for the transfer to occur. If one side is not ready, the other blocks (or times out).

**Fast Path:** When sender and receiver are both ready and the message fits in registers, the kernel performs a direct thread-to-thread transfer without touching the IPC buffer.

**Slow Path:** For larger messages or capability transfers, the kernel copies data via the IPC buffer.

### 4.2 IPC Buffer Layout

Each thread has a 4 KB IPC buffer mapped at a fixed virtual address:

```
Offset  | Field
--------|------------------
0x000   | Message tag (label: 20 bits, length: 6 bits, caps_unwrapped: 3 bits, extra_caps: 3 bits)
0x004   | Badge (set by kernel on receive)
0x008   | MR[0] - Message Register 0
0x00C   | MR[1]
...     | ...
0x1E8   | MR[120] - Last message register
0x1EC   | Cap transfer slots (up to 3)
0x200   | Extended message data (for large transfers)
```

### 4.3 Endpoint States

```
enum EndpointState:
    Idle                        # No threads waiting
    SendBlocked(queue: TcbQueue) # Senders waiting for receiver
    RecvBlocked(queue: TcbQueue) # Receivers waiting for sender
```

### 4.4 IPC Operations

| Operation | Behavior |
|-----------|----------|
| `Send(ep, msg)` | Block until receiver ready, transfer msg, resume receiver |
| `Recv(ep)` | Block until sender ready, receive msg, resume sender |
| `Call(ep, msg)` | Send + Recv atomically (sets up reply cap) |
| `ReplyRecv(reply_cap, reply_msg, ep)` | Reply to caller + Recv next |

### 4.5 Notification Object

```
struct Notification:
    var word: Int               # Bitmap of pending signals
    var bound_tcb: Option<Tcb>  # TCB bound for interrupt delivery
    var wait_queue: TcbQueue    # Threads waiting on this notification
```

Operations:
- `Signal(badge)`: `word |= badge` (non-blocking, never fails)
- `Wait()`: If word != 0, return and clear word. Otherwise block.
- `Poll()`: Non-blocking check: return word and clear, or return 0.

---

## 5. Memory Model

### 5.1 Untyped Memory

At boot, the kernel creates UntypedMemory capabilities for all available physical RAM (minus kernel image and boot structures). These are given to the initial task.

```
struct UntypedMemory:
    val paddr: Int              # Physical base address
    val size_bits: Int          # log2(size in bytes)
    var watermark: Int          # Next free offset within this block
    var children: Int           # Count of retyped children
```

### 5.2 Retype Operation

Retype carves a typed object out of an untyped block:

```
fn retype(untyped_cap: CapSlot, new_type: CapType, size_bits: Int, count: Int) -> Result<List<CapSlot>, Error>:
    # 1. Verify untyped_cap has sufficient remaining space
    # 2. Verify alignment requirements for new_type
    # 3. For each object:
    #    a. Advance watermark
    #    b. Initialize kernel object at watermark address
    #    c. Create capability in caller's CSpace
    # 4. Update MDB: new caps are children of untyped_cap
```

### 5.3 Virtual Address Space (VSpace)

Each process has a VSpace containing a page table hierarchy:

- **x86:** 2-level (Page Directory -> Page Table -> 4KB Page)
- **ARM:** 2-level (L1 -> L2 -> 4KB Page)
- **RISC-V:** 2-level Sv32 (root -> leaf -> 4KB Page)

Mapping a page requires:
1. A Frame capability (physical page)
2. A VSpace capability (address space)
3. PageTable capabilities for intermediate levels
4. Desired virtual address and access rights

---

## 6. Scheduling Model

### 6.1 Data Structures

```
struct Scheduler:
    val queues: List<TcbQueue>     # One queue per priority level (256)
    var current: Option<Tcb>       # Currently running thread
    var idle_thread: Tcb           # Runs when nothing else is runnable
    var need_reschedule: Bool      # Deferred reschedule flag

struct SchedContext:
    val budget: Int                # Total budget per period (microseconds)
    val period: Int                # Replenishment period (microseconds)
    var remaining: Int             # Remaining budget in current period
    var replenish_time: Int        # Absolute time of next replenishment
    var bound_tcb: Option<Tcb>     # Thread using this context
```

### 6.2 Scheduling Algorithm

```
fn pick_next() -> Tcb:
    # 1. Scan priority levels from highest (255) to lowest (0)
    # 2. For each non-empty queue:
    #    a. Peek at head thread
    #    b. Check if thread's SchedContext has remaining budget > 0
    #    c. If yes, dequeue and return
    #    d. If no, check for replenishment eligibility
    # 3. If no runnable thread found, return idle_thread
```

### 6.3 Budget Enforcement

On each timer tick (or on system call return):
1. Charge elapsed time against current thread's SchedContext.remaining
2. If remaining <= 0:
   - Move thread to the back of its priority queue
   - Set need_reschedule = true
3. If current time >= replenish_time:
   - remaining = budget
   - replenish_time += period

### 6.4 Priority Donation During IPC

When thread A (high priority) calls thread B (low priority) via IPC:
1. Thread A's SchedContext is temporarily lent to thread B
2. Thread B runs with thread A's budget and effective priority
3. When thread B replies, the SchedContext returns to thread A

This prevents priority inversion without explicit priority inheritance protocols.

---

## 7. Boot Sequence

### 7.1 x86 Boot Flow

```
1. Multiboot bootloader loads kernel ELF at 0x100000
2. boot_asm.spl:
   a. Set up initial stack (8 KB)
   b. Load GDT (flat segments: kernel code, kernel data, user code, user data, TSS)
   c. Enter protected mode (already in PM from Multiboot)
   d. Call kernel_main()

3. kernel_main() in boot.spl:
   a. Initialize serial port (0x3F8) for debug output
   b. Parse Multiboot info: memory map, kernel boundaries
   c. Initialize frame allocator with available memory
   d. Set up kernel page tables (identity map first 4MB + kernel)
   e. Enable paging
   f. Initialize IDT (256 entries: exceptions, IRQs, syscall)
   g. Initialize PIT timer (1ms tick)
   h. Create initial Untyped capabilities for all free memory
   i. Create initial task:
      - Allocate TCB, CSpace, VSpace from boot Untyped
      - Map user-space binary (init.spl compiled code)
      - Grant all Untyped capabilities to initial task
      - Set initial task as highest priority
   j. Print "[BOOT OK]" to serial
   k. Start scheduler -- context switch to initial task
```

### 7.2 Initial Task Bootstrap

The initial task (user/init.spl) receives:
- Capability to all remaining UntypedMemory
- Capability to all IRQ handler objects
- Capability to all IOPort ranges (x86)
- Its own TCB, CSpace, VSpace, SchedContext capabilities

It then:
1. Creates system servers (device manager, VFS, network) by retyping memory
2. Distributes capabilities to servers as needed
3. Starts application tasks

---

## 8. System Call Interface

### 8.1 Syscall Encoding

On x86, system calls use `int 0x80`:
- EAX = syscall number
- EBX = capability pointer (slot index in caller's CSpace)
- ECX, EDX, ESI, EDI = arguments / first 4 message registers
- Return: EAX = error code, EBX-EDI = return values / message registers

### 8.2 Syscall Dispatch

```
fn syscall_handler(regs: Registers):
    val syscall_num = regs.eax
    val cap_ptr = regs.ebx

    # Lookup capability in caller's CSpace
    val cap = current_thread.cspace.lookup(cap_ptr)
    if cap.? == nil:
        return Error.InvalidCap

    # Dispatch based on syscall number and cap type
    var result = match syscall_num:
        SYSCALL_SEND:       do_send(cap.?, regs)
        SYSCALL_RECV:       do_recv(cap.?, regs)
        SYSCALL_CALL:       do_call(cap.?, regs)
        SYSCALL_REPLY_RECV: do_reply_recv(cap.?, regs)
        SYSCALL_YIELD:      do_yield()
        SYSCALL_RETYPE:     do_retype(cap.?, regs)
        # ... etc
```

### 8.3 Error Codes

```
enum SyscallError:
    Ok                  # 0 - Success
    InvalidCap          # 1 - Capability not found
    InvalidOperation    # 2 - Operation not permitted on this cap type
    InsufficientRights  # 3 - Cap rights insufficient
    RangeError          # 4 - Argument out of range
    AlignmentError      # 5 - Address not properly aligned
    NotEnoughMemory     # 6 - Untyped too small for retype
    DeleteFirst         # 7 - Must delete children before retype
    TruncatedMessage    # 8 - IPC message truncated
```

---

## 9. Architecture HAL

The Hardware Abstraction Layer provides a uniform interface for architecture-specific operations:

```
trait ArchHal:
    fn init_interrupts()
    fn enable_interrupts()
    fn disable_interrupts()
    fn set_timer(microseconds: Int)
    fn context_switch(from: Tcb, to: Tcb)
    fn init_address_space(vspace: VSpace)
    fn map_page(vspace: VSpace, vaddr: Int, paddr: Int, rights: CapRights)
    fn unmap_page(vspace: VSpace, vaddr: Int)
    fn invalidate_tlb(vaddr: Int)
    fn read_time() -> Int
    fn debug_putchar(ch: Int)
    fn halt()
```

Each architecture implements this trait in its `arch/<arch>/` directory.

---

## 10. Kernel Invariants

These invariants must always hold:

1. **Cap integrity:** No user-accessible memory contains a valid kernel object pointer
2. **MDB consistency:** The derivation tree is always a valid doubly-linked list
3. **Scheduling invariant:** Exactly one thread is in the Running state at all times
4. **Budget conservation:** Sum of all SchedContext budgets charged equals elapsed wall-clock time
5. **Memory accounting:** Total memory in Untyped caps + retyped objects = total system RAM
6. **No kernel allocation:** After boot, the kernel never calls a memory allocator
7. **Bounded execution:** No kernel code path iterates over unbounded data (except revoke, which is bounded by the MDB depth)
