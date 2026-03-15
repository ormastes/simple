# Simple OS - Capability System Design

**Version:** 0.1.0
**Status:** Draft
**Last Updated:** 2026-03-15

---

## 1. Overview

The capability system is the cornerstone of Simple OS security. Every resource access -- memory, IPC, scheduling, I/O -- is mediated by capabilities. There is no ambient authority: a thread can only perform an operation if it holds a capability with sufficient rights.

This design is directly inspired by seL4's capability model but adapted for the Simple language's type system and runtime constraints.

---

## 2. Capability Encoding

Each capability is encoded as a 64-bit value internally, but user space refers to capabilities by their CSpace slot index (an integer address). The kernel resolves slot indices to capability structures.

### 2.1 Kernel-Internal Capability Representation

```
struct CapSlot:
    val type_tag: CapType       # Object type (8 bits)
    val rights: CapRights       # Access rights bitmask (8 bits)
    val object_ptr: Int         # Pointer/index to kernel object (48 bits)
    val badge: Int              # Badge for IPC identification
    var mdb_next: Option<CapSlot>   # MDB: next derived capability
    var mdb_prev: Option<CapSlot>   # MDB: previous / parent capability
```

Conceptual bit layout (internal kernel representation):

```
[object_ptr:48 | rights:8 | type:8]
```

### 2.2 Capability Types

```
enum CapType:
    Null            # 0x00 - Empty slot
    Untyped         # 0x01 - Raw physical memory
    Endpoint        # 0x02 - Synchronous IPC endpoint
    Notification    # 0x03 - Async notification object
    CNode           # 0x04 - Capability container node
    TCB             # 0x05 - Thread control block
    SchedContext    # 0x06 - MCS scheduling context
    Frame           # 0x07 - Physical page frame
    PageTable       # 0x08 - Page table structure
    VSpace          # 0x09 - Virtual address space root
    IRQHandler      # 0x0A - Interrupt handler binding
    IOPort          # 0x0B - I/O port range (x86)
    Reply           # 0x0C - One-shot reply capability
```

### 2.3 Access Rights

```
struct CapRights:
    val read: Bool      # bit 0 - Can read / receive
    val write: Bool     # bit 1 - Can write / send
    val grant: Bool     # bit 2 - Can transfer capabilities via IPC
    val revoke: Bool    # bit 3 - Can revoke derived capabilities

# Bitmask representation:
# 0b0001 = Read
# 0b0010 = Write
# 0b0100 = Grant
# 0b1000 = Revoke
# 0b1111 = AllRights
# 0b0000 = NoRights
```

Rights interpretation varies by object type:

| Object Type | Read | Write | Grant | Revoke |
|-------------|------|-------|-------|--------|
| Endpoint | Recv | Send | Transfer caps in IPC | Revoke derived |
| Notification | Wait | Signal | -- | Revoke derived |
| Frame | Map readable | Map writable | -- | Revoke mappings |
| Untyped | -- | Retype | -- | Reclaim children |
| CNode | Lookup | Insert/Delete | -- | Revoke subtree |
| TCB | Read registers | Write registers | -- | -- |
| IOPort | In | Out | -- | -- |

---

## 3. CSpace Architecture

### 3.1 CNode (Capability Node)

A CNode is a kernel object that contains a fixed number of capability slots:

```
struct CNode:
    val slots: List<CapSlot>    # Array of capability slots
    val radix_bits: Int         # log2(number of slots), e.g., 8 means 256 slots
    val guard: Int              # Guard value for this node
    val guard_bits: Int         # Number of bits in the guard
```

The number of slots is always a power of 2: `num_slots = 2^radix_bits`.

### 3.2 CSpace (Capability Space)

A CSpace is a tree of CNodes rooted at a thread's root CNode (stored in its TCB). The tree structure allows compact representation of large capability spaces using guards.

```
struct CSpace:
    val root: CNode             # Root CNode (pointed to by TCB)
```

### 3.3 CSpace Addressing

A capability pointer (cap_ptr) is an integer that encodes the path through the CNode tree:

```
cap_ptr bits: [guard_1 | index_1 | guard_2 | index_2 | ...]
              MSB                                        LSB
```

Lookup algorithm:

```
fn lookup(root: CNode, cap_ptr: Int, bits_remaining: Int) -> Result<CapSlot, Error>:
    # 1. Match guard
    val guard_shift = bits_remaining - root.guard_bits
    val extracted_guard = (cap_ptr >> guard_shift) & mask(root.guard_bits)
    if extracted_guard != root.guard:
        return Error.InvalidCap

    # 2. Extract index
    var remaining = bits_remaining - root.guard_bits
    val index_shift = remaining - root.radix_bits
    val index = (cap_ptr >> index_shift) & mask(root.radix_bits)
    remaining = remaining - root.radix_bits

    # 3. Get slot
    val slot = root.slots[index]

    # 4. If bits consumed, we found it
    if remaining == 0:
        return slot

    # 5. If slot is a CNode, recurse
    if slot.type_tag == CapType.CNode:
        val next_cnode = slot.object_ptr as CNode
        return lookup(next_cnode, cap_ptr, remaining)

    # 6. Otherwise, error
    return Error.InvalidCap
```

### 3.4 CSpace Examples

**Simple flat CSpace (single CNode):**

```
Root CNode: guard=0, guard_bits=0, radix_bits=12
Total slots: 4096
cap_ptr is just the 12-bit index

Slot 0: TCB (self)
Slot 1: CNode (self)
Slot 2: VSpace (own address space)
Slot 3: Endpoint (IPC to init)
...
Slot 4095: (empty)
```

**Two-level CSpace:**

```
Root CNode: guard=0, guard_bits=0, radix_bits=8  (256 slots)
  Slot 0: CNode (level-2, guard=0, guard_bits=0, radix_bits=8)
    Slot 0..255: capabilities for process services
  Slot 1: CNode (level-2, guard=0, guard_bits=0, radix_bits=8)
    Slot 0..255: capabilities for device drivers
  ...

cap_ptr = [level1_index:8 | level2_index:8] = 16-bit address
Total addressable slots: 256 * 256 = 65536
```

---

## 4. Capability Operations

### 4.1 Mint

Create a new capability derived from an existing one, with equal or reduced rights:

```
fn mint(src_cnode: CapSlot, src_index: Int, dest_cnode: CapSlot, dest_index: Int, new_rights: CapRights, new_badge: Int) -> Result<Nil, Error>:
    # 1. Lookup source slot
    val src = src_cnode.lookup(src_index)
    if src.type_tag == CapType.Null:
        return Error.InvalidCap

    # 2. Verify new_rights is subset of src.rights
    if not rights_subset(new_rights, src.rights):
        return Error.InsufficientRights

    # 3. Verify dest slot is empty
    val dest = dest_cnode.lookup(dest_index)
    if dest.type_tag != CapType.Null:
        return Error.DeleteFirst

    # 4. Create new cap with reduced rights
    val minted = CapSlot(
        type_tag: src.type_tag,
        rights: new_rights,
        object_ptr: src.object_ptr,
        badge: new_badge
    )

    # 5. Insert into MDB as child of src
    mdb_insert_after(src, minted)

    # 6. Place in destination slot
    dest_cnode.slots[dest_index] = minted
    return Ok(nil)
```

### 4.2 Copy

Copy a capability to another slot (same rights, same badge):

```
fn copy(src_cnode: CapSlot, src_index: Int, dest_cnode: CapSlot, dest_index: Int) -> Result<Nil, Error>:
    return mint(src_cnode, src_index, dest_cnode, dest_index, src.rights, src.badge)
```

### 4.3 Delete

Remove a capability from a slot:

```
fn delete(cnode: CapSlot, index: Int) -> Result<Nil, Error>:
    val slot = cnode.lookup(index)
    if slot.type_tag == CapType.Null:
        return Ok(nil)  # Already empty

    # 1. Remove from MDB
    mdb_remove(slot)

    # 2. If this was the last cap to the object, finalize the object
    if not mdb_has_other_refs(slot):
        finalize_object(slot)

    # 3. Clear the slot
    slot.type_tag = CapType.Null
    slot.object_ptr = 0
    return Ok(nil)
```

### 4.4 Revoke

Revoke a capability and all capabilities derived from it:

```
fn revoke(cnode: CapSlot, index: Int) -> Result<Nil, Error>:
    val slot = cnode.lookup(index)
    if slot.type_tag == CapType.Null:
        return Ok(nil)

    # Walk MDB and delete all descendants
    var child = mdb_first_child(slot)
    while child.? != nil:
        val next = mdb_next_sibling(child.?)
        # Recursively revoke children first
        revoke_subtree(child.?)
        # Then delete this child
        delete_cap(child.?)
        child = next

    return Ok(nil)
```

**Important:** Revoke on an Untyped capability destroys all objects created from that memory, effectively reclaiming it. This is the only way to "free" memory in Simple OS.

---

## 5. Mapping Database (MDB)

The MDB tracks the derivation hierarchy of all capabilities. It is organized as a doubly-linked list sorted by object address and derivation depth.

### 5.1 MDB Structure

```
# Each CapSlot has:
var mdb_next: Option<CapSlot>   # Next cap in MDB order
var mdb_prev: Option<CapSlot>   # Previous cap in MDB order

# Derivation relationship:
# Parent is the cap from which this cap was derived (via mint, copy, or retype)
# Children are caps derived from this cap
```

### 5.2 MDB Invariants

1. All capabilities to the same object are contiguous in the MDB list
2. A parent always appears before its children in MDB order
3. The MDB is acyclic
4. Every non-original capability has exactly one parent in the MDB

### 5.3 MDB Operations

| Operation | Description |
|-----------|-------------|
| `mdb_insert_after(parent, new_cap)` | Insert new_cap after parent in MDB |
| `mdb_remove(cap)` | Remove cap from MDB (does not affect children) |
| `mdb_first_child(cap)` | Find first child of cap in MDB |
| `mdb_next_sibling(cap)` | Find next sibling at same derivation depth |
| `mdb_has_other_refs(cap)` | Check if object has other capability references |

---

## 6. Initial Capability Distribution

At boot, the kernel creates the initial task with a CSpace containing capabilities to all system resources:

```
Initial Task CSpace (Root CNode, 4096 slots):

Slot  0: TCB         (self, AllRights)
Slot  1: CNode       (self root CNode, AllRights)
Slot  2: VSpace      (self address space, AllRights)
Slot  3: SchedContext (self scheduling context, AllRights)
Slot  4: Reply        (boot reply cap -- unused)
Slot  5: Endpoint     (fault handler endpoint)

# Untyped memory caps (one per physical region):
Slot 16: Untyped (0x200000 - 0x400000, 2MB)
Slot 17: Untyped (0x400000 - 0x800000, 4MB)
Slot 18: Untyped (0x800000 - 0x1000000, 8MB)
...

# Device memory (MMIO regions):
Slot 64: Untyped (0xB8000 - 0xB9000, VGA, 4KB, device)
Slot 65: Untyped (0xFEC00000, IO APIC, 4KB, device)
Slot 66: Untyped (0xFEE00000, Local APIC, 4KB, device)

# IRQ handler caps:
Slot 128: IRQHandler (IRQ 0 - Timer)
Slot 129: IRQHandler (IRQ 1 - Keyboard)
Slot 130: IRQHandler (IRQ 2 - Cascade)
...
Slot 143: IRQHandler (IRQ 15 - Secondary ATA)

# I/O port caps (x86 only):
Slot 192: IOPort (0x0000 - 0xFFFF, all ports)

# Reserved for init task use:
Slot 256..4095: (empty, available for init to populate)
```

---

## 7. Capability Transfer via IPC

Capabilities can be transferred between threads during IPC if the sender holds a capability with Grant rights on the endpoint:

### 7.1 Transfer Protocol

1. Sender places capability slot indices in the IPC buffer's cap transfer area
2. Sender sets `extra_caps` field in the message tag
3. On transfer, the kernel:
   a. Looks up each capability in the sender's CSpace
   b. Verifies sender has Grant right on the endpoint
   c. Derives a new capability (mint with same rights) in the receiver's CSpace
   d. Updates the MDB to reflect the new derivation
4. Receiver finds the transferred caps in its designated receive slots

### 7.2 Badge Mechanism

When a capability to an Endpoint is minted with a badge value, all messages sent through that capability carry the badge. The receiver can use the badge to identify which client sent the message:

```
# Server creates badged endpoint caps for clients:
val client1_ep = mint(server_ep, rights: SendOnly, badge: 1)
val client2_ep = mint(server_ep, rights: SendOnly, badge: 2)

# When server receives, the badge identifies the sender:
# recv() returns badge=1 for client1, badge=2 for client2
```

---

## 8. Security Properties

### 8.1 Confinement

A process can be confined (prevented from communicating with the outside world) by not giving it any Endpoint capabilities with Send rights and no Grant rights on any capability.

### 8.2 Authority Propagation

Authority can only propagate through:
1. Explicit capability transfer via IPC (requires Grant right)
2. Capability minting/copying (requires access to both source and destination CNodes)

### 8.3 Revocation Guarantees

- Revoking a capability removes all access derived from it
- Revoking an Untyped capability destroys all objects and reclaims memory
- Revocation is transitive: revoking cap A also revokes all caps derived from A

### 8.4 Information Flow Control

By carefully controlling capability distribution, the initial task (root server) can enforce arbitrary information flow policies between processes. The kernel provides the mechanism; the policy is in user space.
