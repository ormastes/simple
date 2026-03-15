# Simple OS - IPC Design

**Version:** 0.1.0
**Status:** Draft
**Last Updated:** 2026-03-15

---

## 1. Overview

Simple OS IPC follows the L4 microkernel tradition: synchronous rendezvous for structured message passing, and asynchronous notifications for lightweight signaling. All IPC is mediated by kernel objects (Endpoints and Notifications) accessed through capabilities.

---

## 2. Synchronous IPC (Rendezvous)

### 2.1 Core Principle

Synchronous IPC requires both the sender and receiver to be ready simultaneously. The kernel directly transfers data from sender to receiver without intermediate buffering (in the fast path). This minimizes latency and avoids copy overhead.

### 2.2 Endpoint Object

An Endpoint is a kernel object that serves as a rendezvous point for IPC:

```
struct Endpoint:
    var state: EndpointState
    var queue: TcbQueue         # Queue of waiting threads

enum EndpointState:
    Idle                        # No threads waiting
    SendBlocked                 # Queue contains blocked senders
    RecvBlocked                 # Queue contains blocked receivers
```

**Key property:** An Endpoint never has both senders and receivers queued simultaneously. It is either idle, has a sender queue, or has a receiver queue.

### 2.3 IPC Operations

#### 2.3.1 Send

```
fn do_send(ep_cap: CapSlot, sender: Tcb) -> Result<Nil, Error>:
    # Verify Write right (Send requires Write)
    if not ep_cap.rights.write:
        return Error.InsufficientRights

    val ep = ep_cap.object_ptr as Endpoint

    match ep.state:
        RecvBlocked:
            # Receiver is waiting -- transfer immediately
            val receiver = ep.queue.dequeue()
            transfer_message(sender, receiver, ep_cap.badge)
            if ep.queue.is_empty():
                ep.state = Idle
            set_running(receiver)
            return Ok(nil)

        Idle:
            # No receiver -- block sender
            ep.state = SendBlocked
            ep.queue.enqueue(sender)
            sender.state = ThreadState.BlockedOnSend
            schedule()  # Pick another thread
            return Ok(nil)

        SendBlocked:
            # Other senders already waiting -- join the queue
            ep.queue.enqueue(sender)
            sender.state = ThreadState.BlockedOnSend
            schedule()
            return Ok(nil)
```

#### 2.3.2 Recv

```
fn do_recv(ep_cap: CapSlot, receiver: Tcb) -> Result<Nil, Error>:
    # Verify Read right (Recv requires Read)
    if not ep_cap.rights.read:
        return Error.InsufficientRights

    val ep = ep_cap.object_ptr as Endpoint

    # Check bound notification first (for interrupt delivery)
    if val ntfn = receiver.bound_notification:
        if ntfn.word != 0:
            # Notification pending -- deliver it instead of blocking
            receiver.ipc_buffer.set_badge(ntfn.word)
            ntfn.word = 0
            return Ok(nil)

    match ep.state:
        SendBlocked:
            # Sender is waiting -- transfer immediately
            val sender = ep.queue.dequeue()
            transfer_message(sender, receiver, sender.send_badge)
            if ep.queue.is_empty():
                ep.state = Idle
            set_running(sender)
            return Ok(nil)

        Idle:
            # No sender -- block receiver
            ep.state = RecvBlocked
            ep.queue.enqueue(receiver)
            receiver.state = ThreadState.BlockedOnRecv
            schedule()
            return Ok(nil)

        RecvBlocked:
            # Other receivers already waiting -- join the queue
            ep.queue.enqueue(receiver)
            receiver.state = ThreadState.BlockedOnRecv
            schedule()
            return Ok(nil)
```

#### 2.3.3 Call (Send + Recv)

Call is a combined Send + Recv that atomically sends a message and then waits for a reply:

```
fn do_call(ep_cap: CapSlot, caller: Tcb) -> Result<Nil, Error>:
    # 1. Create a one-shot Reply capability
    val reply_cap = create_reply_cap(caller)

    # 2. Set up the caller for a reply wait
    caller.reply_cap = reply_cap

    # 3. Send the message (includes reply cap in transfer)
    do_send(ep_cap, caller)

    # 4. After send completes, caller blocks waiting for reply
    caller.state = ThreadState.BlockedOnReply
    schedule()
    return Ok(nil)
```

#### 2.3.4 ReplyRecv

ReplyRecv atomically replies to the previous caller and waits for the next message. This is the core server loop operation:

```
fn do_reply_recv(reply_cap: CapSlot, ep_cap: CapSlot, server: Tcb) -> Result<Nil, Error>:
    # 1. Reply to the previous caller
    if reply_cap.type_tag == CapType.Reply:
        val caller = reply_cap.object_ptr as Tcb
        transfer_message(server, caller, 0)
        caller.state = ThreadState.Running
        # Delete the one-shot reply cap
        delete_reply_cap(reply_cap)

    # 2. Wait for next message on the endpoint
    return do_recv(ep_cap, server)
```

---

## 3. IPC Buffer

### 3.1 Structure

Each thread has a 4 KB IPC buffer mapped at a virtual address determined during TCB configuration:

```
struct IpcBuffer:
    var tag: MessageTag         # Message metadata
    var badge: Int              # Badge value (set by kernel on recv)
    var mrs: List<Int>          # Message registers (MR[0]..MR[119])
    var caps: List<Int>         # Capability transfer slot indices
    var recv_slots: List<Int>   # Slots in CSpace for receiving caps
```

### 3.2 Message Tag

```
struct MessageTag:
    val label: Int              # Application-defined label (20 bits)
    val length: Int             # Number of message registers used (6 bits, max 63)
    val extra_caps: Int         # Number of capabilities to transfer (3 bits, max 7)
    val caps_unwrapped: Int     # Bitmap: which extra_caps were unwrapped (3 bits)
```

### 3.3 Message Registers

The first 4 message registers (MR[0]..MR[3]) are passed in CPU registers for fast-path IPC:

| Architecture | Register MR[0] | MR[1] | MR[2] | MR[3] |
|-------------|----------------|--------|--------|--------|
| x86 | ECX | EDX | ESI | EDI |
| ARM | R2 | R3 | R4 | R5 |
| RISC-V | a2 | a3 | a4 | a5 |

Remaining message registers (MR[4]..MR[119]) are stored in the IPC buffer in memory.

### 3.4 Buffer Layout (Byte Offsets)

```
Offset   Size    Field
0x000    4       Message Tag
0x004    4       Badge
0x008    4       MR[0]
0x00C    4       MR[1]
0x010    4       MR[2]
0x014    4       MR[3]
0x018    4       MR[4]
...
0x1E4    4       MR[119]
0x1E8    4       extra_caps[0] (CSpace index)
0x1EC    4       extra_caps[1]
0x1F0    4       extra_caps[2]
0x1F4    4       extra_caps[3]
0x1F8    4       extra_caps[4]
0x1FC    4       extra_caps[5]
0x200    4       extra_caps[6]
0x204    4       recv_slot[0] (CSpace index for receiving)
0x208    4       recv_slot[1]
0x20C    4       recv_slot[2]
0x210    4       recv_slot[3]
0x214    4       recv_slot[4]
0x218    4       recv_slot[5]
0x21C    4       recv_slot[6]
0x220..0xFFF     (reserved / padding)
```

---

## 4. Message Transfer

### 4.1 Fast Path

The fast path handles the common case: short messages (4 MRs), no capability transfer, direct sender-to-receiver handoff.

```
fn transfer_message_fast(sender: Tcb, receiver: Tcb, badge: Int):
    # Transfer happens entirely in registers -- no memory access
    receiver.regs.mr0 = sender.regs.mr0
    receiver.regs.mr1 = sender.regs.mr1
    receiver.regs.mr2 = sender.regs.mr2
    receiver.regs.mr3 = sender.regs.mr3
    receiver.ipc_buffer.tag = sender.ipc_buffer.tag
    receiver.ipc_buffer.badge = badge
```

Fast path conditions:
1. Message length <= 4 (fits in registers)
2. No capability transfers (extra_caps == 0)
3. Both threads are in the same scheduling domain
4. No timeout or fault handling needed

### 4.2 Slow Path

The slow path handles longer messages and capability transfers:

```
fn transfer_message(sender: Tcb, receiver: Tcb, badge: Int):
    val tag = sender.ipc_buffer.tag

    # Transfer register-based MRs
    receiver.regs.mr0 = sender.regs.mr0
    receiver.regs.mr1 = sender.regs.mr1
    receiver.regs.mr2 = sender.regs.mr2
    receiver.regs.mr3 = sender.regs.mr3

    # Transfer memory-based MRs
    var i = 4
    while i < tag.length:
        receiver.ipc_buffer.mrs[i] = sender.ipc_buffer.mrs[i]
        i = i + 1

    # Transfer capabilities
    var c = 0
    while c < tag.extra_caps:
        val src_slot = sender.ipc_buffer.caps[c]
        val dst_slot = receiver.ipc_buffer.recv_slots[c]
        val cap = sender.cspace.lookup(src_slot)
        if cap.? != nil:
            # Derive cap into receiver's CSpace
            derive_cap(cap.?, receiver.cspace, dst_slot)
        c = c + 1

    receiver.ipc_buffer.tag = tag
    receiver.ipc_buffer.badge = badge
```

---

## 5. Notifications (Asynchronous IPC)

### 5.1 Notification Object

```
struct Notification:
    var word: Int               # Bitmask of pending signals (32 or 64 bits)
    var state: NotificationState
    var wait_queue: TcbQueue    # Threads blocked on Wait
    var bound_tcb: Option<Tcb>  # TCB bound for interrupt delivery

enum NotificationState:
    Idle                        # word == 0, no waiters
    Active                      # word != 0, signals pending
    Waiting                     # Threads in wait_queue
```

### 5.2 Signal Operation

Signal is non-blocking and never fails (assuming valid capability):

```
fn do_signal(ntfn_cap: CapSlot) -> Result<Nil, Error>:
    if not ntfn_cap.rights.write:
        return Error.InsufficientRights

    val ntfn = ntfn_cap.object_ptr as Notification
    val badge = ntfn_cap.badge

    match ntfn.state:
        Waiting:
            # Wake up one waiter with the badge
            val waiter = ntfn.wait_queue.dequeue()
            waiter.ipc_buffer.badge = badge
            if ntfn.wait_queue.is_empty():
                ntfn.state = Idle
            set_running(waiter)

        Idle:
            # Set bits and transition to Active
            ntfn.word = ntfn.word | badge
            ntfn.state = Active

        Active:
            # OR in more bits
            ntfn.word = ntfn.word | badge
```

### 5.3 Wait Operation

```
fn do_wait(ntfn_cap: CapSlot, thread: Tcb) -> Result<Nil, Error>:
    if not ntfn_cap.rights.read:
        return Error.InsufficientRights

    val ntfn = ntfn_cap.object_ptr as Notification

    match ntfn.state:
        Active:
            # Return accumulated signals and clear
            thread.ipc_buffer.badge = ntfn.word
            ntfn.word = 0
            ntfn.state = Idle
            return Ok(nil)

        Idle:
            # No signals -- block
            ntfn.state = Waiting
            ntfn.wait_queue.enqueue(thread)
            thread.state = ThreadState.BlockedOnNotification
            schedule()
            return Ok(nil)

        Waiting:
            # Other threads already waiting -- join queue
            ntfn.wait_queue.enqueue(thread)
            thread.state = ThreadState.BlockedOnNotification
            schedule()
            return Ok(nil)
```

### 5.4 Poll Operation

Non-blocking check for pending signals:

```
fn do_poll(ntfn_cap: CapSlot) -> Result<Int, Error>:
    val ntfn = ntfn_cap.object_ptr as Notification
    if ntfn.state == Active:
        val result = ntfn.word
        ntfn.word = 0
        ntfn.state = Idle
        return Ok(result)
    return Ok(0)
```

---

## 6. Fault Delivery via IPC

### 6.1 Fault Types

```
enum FaultType:
    CapFault(address: Int, in_recv_phase: Bool)
    VMFault(address: Int, is_instruction: Bool, fsr: Int)
    UnknownSyscall(syscall_num: Int)
    UserException(number: Int, code: Int)
    Timeout(data: Int)
```

### 6.2 Fault Delivery

When a thread faults, the kernel sends a fault message to the thread's designated fault handler endpoint:

```
fn deliver_fault(faulting: Tcb, fault: FaultType):
    val handler_ep = faulting.fault_handler
    if handler_ep.? == nil:
        # No fault handler -- suspend thread
        faulting.state = ThreadState.Inactive
        return

    # Construct fault IPC message
    var msg = IpcMessage()
    msg.tag.label = FAULT_LABEL
    match fault:
        VMFault(address, is_instruction, fsr):
            msg.set_mr(0, FAULT_VM)
            msg.set_mr(1, address)
            msg.set_mr(2, if is_instruction: 1 else: 0)
            msg.set_mr(3, fsr)
            msg.tag.length = 4

        CapFault(address, in_recv):
            msg.set_mr(0, FAULT_CAP)
            msg.set_mr(1, address)
            msg.set_mr(2, if in_recv: 1 else: 0)
            msg.tag.length = 3

        # ... other fault types

    # Send fault message (kernel acts as sender)
    # Faulting thread blocks until handler replies
    faulting.state = ThreadState.BlockedOnFault
    do_send_from_kernel(handler_ep.?, msg, faulting)
```

### 6.3 Fault Handler Protocol

The fault handler (typically a pager or supervisor process):

1. Receives the fault IPC message
2. Examines fault details in message registers
3. Takes corrective action (e.g., maps a page for a page fault)
4. Replies to the faulting thread to resume it

```
# Example: simple page fault handler
fn handle_faults(ep_cap: Int):
    while true:
        val msg = recv(ep_cap)
        val fault_type = msg.get_mr(0)
        if fault_type == FAULT_VM:
            val fault_addr = msg.get_mr(1)
            # Map a page at the faulting address
            val frame = alloc_frame()
            map_page(faulting_vspace, fault_addr, frame)
            # Reply to resume the faulting thread
            reply(msg)
```

---

## 7. IPC Timeouts

### 7.1 Timeout Mechanism

Each IPC operation can specify a timeout (in microseconds):

- **0:** Non-blocking (poll semantics)
- **MAX_INT:** Infinite wait (block forever)
- **Other:** Block for up to N microseconds

```
fn do_send_with_timeout(ep_cap: CapSlot, sender: Tcb, timeout_us: Int) -> Result<Nil, Error>:
    if timeout_us == 0:
        # Non-blocking: check if receiver is ready
        val ep = ep_cap.object_ptr as Endpoint
        if ep.state != RecvBlocked:
            return Error.WouldBlock
        # ... proceed with transfer

    # Set up timeout
    if timeout_us != MAX_INT:
        sender.timeout_deadline = read_time() + timeout_us
        timer_set_timeout(sender)

    # Block as normal
    do_send(ep_cap, sender)
```

### 7.2 Timeout Delivery

When a timeout fires:
1. The timer interrupt handler checks the blocked thread's deadline
2. If the deadline has passed, the thread is unblocked with a Timeout error
3. The thread is removed from the endpoint's wait queue

---

## 8. IPC Performance Considerations

### 8.1 Fast Path Optimization

The fast path is the critical performance path. Optimizations:

1. **Register-only transfer:** First 4 MRs in CPU registers, no memory access
2. **Direct switch:** Context switch directly from sender to receiver (no scheduler involvement)
3. **Single capability lookup:** Cache the endpoint pointer after first lookup
4. **No allocation:** IPC buffers are pre-allocated per thread

### 8.2 Expected Performance

| Operation | Target Cycles (x86) |
|-----------|---------------------|
| Fast-path Send+Recv | < 400 |
| Fast-path Call+Reply | < 800 |
| Slow-path (full buffer) | < 2000 |
| Signal notification | < 100 |
| Wait on notification | < 200 |
| Fault delivery + reply | < 1500 |

### 8.3 Scalability

- Endpoint queues are O(1) enqueue/dequeue (linked list)
- No global locks in the IPC path
- Per-thread IPC buffers avoid contention
- Notification word uses atomic OR for signal (future SMP support)
