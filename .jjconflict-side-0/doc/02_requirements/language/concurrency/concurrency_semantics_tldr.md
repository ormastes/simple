# Simple Concurrency Semantics — TL;DR

**25 decisions (REQ-CONC-001..025), all PROPOSED. See `concurrency_semantics.md`.**

```sdn
node ConcurrencyModel {
  label: "Simple Concurrency Semantics"
  children: [
    node Scheduling {
      S3_fairness:       "no starvation-freedom guarantee; insert green_yield() in tight loops (REQ-CONC-001)"
      S4_blocking_io:    "blocks carrier; no thread expansion; use async I/O inside green tasks (REQ-CONC-002)"
      S5_order:          "cooperative_green = FIFO; multicore_green = no order guarantee (REQ-CONC-003)"
    }
    node Cancellation {
      C2_no_force_kill:  "cooperative only; no force-kill; OS exit() is the only hard stop (REQ-CONC-004)"
      C3_cancel_safety:  "channel ops are cancel-safe; stream I/O is not (REQ-CONC-005)"
      C6_recv_unblocks:  "cancel on recv() raises CancellationError; message NOT consumed (REQ-CONC-006)"
    }
    node Errors {
      E1_unhandled:      "stored in handle; surfaces on join(); discarded on handle-drop (REQ-CONC-007)"
      E2_identity:       "nogc = deep copy; gc = reference copy; no type erasure (REQ-CONC-008)"
      E4_siblings:       "first error wins; siblings cancelled; scope waits for cleanup (REQ-CONC-009)"
    }
    node Isolation {
      I2_no_shared_mut:  "no shared mutable across tasks; use Mutex/channel (REQ-CONC-010)"
      I3_happens_before: "send→recv; spawn→first-op; all-ops→join; no other cross-task order (REQ-CONC-011)"
      I5_actor_identity: "new ActorId on restart; old ID → SendResult::closed (REQ-CONC-012)"
    }
    node Channels {
      M1_closed_send:    "SendResult::closed regardless of crash/orderly; use monitor for distinction (REQ-CONC-013)"
      M2_closed_recv:    "drained+closed → Err(Closed); empty+open → suspend (REQ-CONC-014)"
      M5_no_selective:   "FIFO only; no mailbox scan; use typed union + dispatch (REQ-CONC-015)"
      M6_no_nil_block:   "no null channels; Option<Channel> requires explicit unwrap (REQ-CONC-016)"
    }
    node Lifecycle {
      L1_scoped_no_leak: "task_scope guarantees no leaks; unscoped spawn = explicit fire-and-forget (REQ-CONC-017)"
      L2_zombie:         "result buffered in handle; handle-drop frees result (REQ-CONC-018)"
      L3_detached:       "green_spawn_detached() supported; error silently discarded (REQ-CONC-019)"
      L4_actor_gc:       "freed when: task complete + refs zero + mailbox drained (REQ-CONC-020)"
    }
    node Backpressure {
      B2_pipeline:       "bounded channels propagate backpressure via SendResult::full + retry (REQ-CONC-021)"
      B3_timeout:        "recv timeout = no message consumed; channel state unchanged (REQ-CONC-022)"
    }
    node Coroutines {
      CO2_error:         "error → Err result to resumer; dead coro → Err(Dead) (REQ-CONC-023)"
      CO3_yield_value:   "yield(v) → resumer; resume(co, v) → yield return value (REQ-CONC-024)"
    }
    node GC {
      G1_frame_retention: "suspended frame pins locals; drop large objects before await (REQ-CONC-025)"
    }
  ]
}
```

**3 most consequential decisions:**
1. **REQ-CONC-011 (I-3 happens-before)** — pins the entire memory model; without this, all concurrent correctness claims are undefined.
2. **REQ-CONC-007 (E-1 unhandled error)** — chose Kotlin `async` model (handle-captured, not process-crash); shapes all error-handling patterns.
3. **REQ-CONC-002 (S-4 blocking I/O)** — no thread expansion; blocking in `cooperative_green` stalls the carrier; callers must use async I/O.
