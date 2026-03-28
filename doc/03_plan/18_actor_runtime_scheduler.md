# Actor Runtime Scheduler Implementation Plan

## Overview

This plan describes how to implement the Actor instructions (ActorSpawn, ActorSend, ActorRecv) in the codegen, replacing the current trap codes 33-35.

## Current State

### MIR Instructions (mir/types.rs)

```rust
ActorSpawn { dest: VReg, body_block: BlockId }  // Creates new actor, returns handle
ActorSend { actor: VReg, message: VReg }        // Sends message to actor
ActorRecv { dest: VReg }                        // Receives message (blocking)
```

### Existing Runtime Infrastructure (runtime/concurrency/mod.rs)

- `Scheduler` - Global scheduler with mailboxes and join handles
- `spawn_actor(f)` - Spawns actor thread with mailbox setup
- `send_to(id, msg)` - Sends message via scheduler
- `join_actor(id)` - Joins actor thread
- `ActorHandle` - Contains id, inbox_sender, outbox_receiver, join_handle

### Current Codegen Status

All three instructions currently trap:
- Trap 33: ActorSpawn
- Trap 34: ActorSend
- Trap 35: ActorRecv

---

## Implementation Plan

### Phase 1: Runtime FFI Functions

Add FFI-safe actor functions to `src/runtime/src/value.rs`:

```rust
// ============================================================================
// Actor operations (FFI-safe)
// ============================================================================

/// RuntimeActor - heap-allocated actor handle
#[repr(C)]
pub struct RuntimeActor {
    pub header: HeapHeader,
    pub id: u64,
    pub inbox_ptr: *mut u8,   // Pointer to mpsc::Sender<Message>
    pub outbox_ptr: *mut u8,  // Pointer to mpsc::Receiver<Message>
}

/// Spawn a new actor. body_func is a function pointer to the actor body.
/// Returns RuntimeValue containing actor handle.
#[no_mangle]
pub extern "C" fn rt_actor_spawn(body_func: u64) -> RuntimeValue {
    // 1. Allocate RuntimeActor structure
    // 2. Create inbox/outbox channels
    // 3. Spawn thread that calls body_func
    // 4. Register with global scheduler
    // 5. Return RuntimeValue wrapping RuntimeActor
}

/// Send a message to an actor.
/// actor: RuntimeValue containing RuntimeActor
/// message: RuntimeValue to send
#[no_mangle]
pub extern "C" fn rt_actor_send(actor: RuntimeValue, message: RuntimeValue) {
    // 1. Extract RuntimeActor from actor value
    // 2. Serialize message to Message format
    // 3. Send via inbox channel
}

/// Receive a message from the current actor's mailbox.
/// Returns RuntimeValue containing the message, or NIL if timeout.
#[no_mangle]
pub extern "C" fn rt_actor_recv() -> RuntimeValue {
    // 1. Get current actor's outbox receiver (thread-local)
    // 2. Block on receive (or with timeout)
    // 3. Deserialize message to RuntimeValue
    // 4. Return message
}

/// Join an actor (wait for completion).
#[no_mangle]
pub extern "C" fn rt_actor_join(actor: RuntimeValue) -> RuntimeValue {
    // 1. Extract RuntimeActor from actor value
    // 2. Wait on join handle
    // 3. Return result or error
}
```

### Phase 2: Thread-Local Actor Context

For `rt_actor_recv` to work, each actor thread needs access to its mailbox:

```rust
// Thread-local storage for current actor context
thread_local! {
    static CURRENT_ACTOR: RefCell<Option<ActorContext>> = RefCell::new(None);
}

struct ActorContext {
    id: u64,
    inbox: mpsc::Receiver<Message>,
    outbox: mpsc::Sender<Message>,
}

fn with_actor_context<F, R>(f: F) -> Option<R>
where
    F: FnOnce(&ActorContext) -> R,
{
    CURRENT_ACTOR.with(|ctx| ctx.borrow().as_ref().map(f))
}
```

### Phase 3: Codegen Declarations (cranelift.rs, jit.rs)

Add runtime function declarations:

```rust
// rt_actor_spawn(body_func: u64) -> RuntimeValue
let mut sig = Signature::new(call_conv);
sig.params.push(AbiParam::new(types::I64));
sig.returns.push(AbiParam::new(types::I64));
let id = module.declare_function("rt_actor_spawn", Linkage::Import, &sig)?;
funcs.insert("rt_actor_spawn", id);

// rt_actor_send(actor: RuntimeValue, message: RuntimeValue)
let mut sig = Signature::new(call_conv);
sig.params.push(AbiParam::new(types::I64));
sig.params.push(AbiParam::new(types::I64));
let id = module.declare_function("rt_actor_send", Linkage::Import, &sig)?;
funcs.insert("rt_actor_send", id);

// rt_actor_recv() -> RuntimeValue
let mut sig = Signature::new(call_conv);
sig.returns.push(AbiParam::new(types::I64));
let id = module.declare_function("rt_actor_recv", Linkage::Import, &sig)?;
funcs.insert("rt_actor_recv", id);
```

### Phase 4: Codegen Implementation

Replace trap instructions with FFI calls:

```rust
MirInst::ActorSpawn { dest, body_block } => {
    let spawn_id = self.runtime_funcs["rt_actor_spawn"];
    let spawn_ref = self.module.declare_func_in_func(spawn_id, builder.func);

    // Get function pointer for body_block
    // Note: body_block needs to be compiled as a separate function
    let body_func_ptr = self.get_block_func_ptr(body_block, builder);

    let call = builder.ins().call(spawn_ref, &[body_func_ptr]);
    let result = builder.inst_results(call)[0];
    vreg_values.insert(*dest, result);
}

MirInst::ActorSend { actor, message } => {
    let send_id = self.runtime_funcs["rt_actor_send"];
    let send_ref = self.module.declare_func_in_func(send_id, builder.func);

    let actor_val = vreg_values[actor];
    let msg_val = vreg_values[message];
    builder.ins().call(send_ref, &[actor_val, msg_val]);
}

MirInst::ActorRecv { dest } => {
    let recv_id = self.runtime_funcs["rt_actor_recv"];
    let recv_ref = self.module.declare_func_in_func(recv_id, builder.func);

    let call = builder.ins().call(recv_ref, &[]);
    let result = builder.inst_results(call)[0];
    vreg_values.insert(*dest, result);
}
```

---

## Design Decisions

### Body Block Compilation

The `body_block` in `ActorSpawn` is a BlockId referencing a block of MIR instructions. Options:

1. **Outline as separate function**: During MIR lowering, extract actor body blocks as separate functions with a standard signature `fn(inbox: Receiver, outbox: Sender)`.

2. **Closure-based**: Wrap body block in a closure that captures necessary variables.

3. **Trampoline**: Generate a trampoline function that sets up actor context and jumps to body block.

**Recommendation**: Option 1 (outline as separate function) is cleanest and matches the existing closure compilation pattern.

### Message Serialization

Messages need to cross thread boundaries. Options:

1. **RuntimeValue directly**: Pass RuntimeValue as-is (requires careful handling of heap pointers)
2. **Serialization**: Convert to bytes and deserialize on receive
3. **Copy semantics**: Deep-copy values for message passing

**Recommendation**: Option 1 with heap reference counting for simple implementation, migrate to Option 3 for safety later.

### Blocking vs Non-blocking Recv

Current design has `ActorRecv` as blocking. Future enhancements:

- Add `ActorTryRecv { dest, timeout }` for non-blocking receive
- Add `ActorSelect { dest, actors, timeout }` for multi-actor select

---

## Testing Strategy

### Unit Tests (runtime)

```rust
#[test]
fn test_rt_actor_spawn_send_recv() {
    let actor = rt_actor_spawn(test_echo_actor as u64);
    rt_actor_send(actor, RuntimeValue::from_int(42));
    let result = rt_actor_recv();
    assert_eq!(result.as_int(), 42);
}
```

### Integration Tests (driver)

```rust
#[test]
fn test_actor_ping_pong() {
    let src = r#"
        actor pong:
            msg = recv()
            send(msg + 1)

        main:
            p = spawn pong
            send(p, 10)
            result = recv()
            return result  # Should be 11
    "#;
    assert_eq!(runner.run_source(src), 11);
}
```

---

## Implementation Order

1. Add `RuntimeActor` struct to value.rs
2. Add thread-local `ActorContext`
3. Implement `rt_actor_spawn` (basic, single message)
4. Implement `rt_actor_send`
5. Implement `rt_actor_recv`
6. Add codegen declarations to both AOT and JIT
7. Replace trap code with FFI calls
8. Add unit tests
9. Add integration tests

---

## Estimated Effort

| Task | Effort |
|------|--------|
| Runtime FFI functions | 2-3 hours |
| Thread-local context | 1 hour |
| Codegen declarations | 30 min |
| Codegen implementation | 1-2 hours |
| Body block compilation | 2-3 hours |
| Testing | 2 hours |
| **Total** | **8-12 hours** |

---

## Dependencies

- Existing `runtime::concurrency` module
- `simple_common::actor` types
- Closure compilation pattern (already implemented)

## Future Enhancements

- Work-stealing scheduler (replace per-actor threads)
- Supervision trees (restart/stop semantics)
- Actor linking (propagate failures)
- Timeouts on recv
- Actor select (wait on multiple actors)
