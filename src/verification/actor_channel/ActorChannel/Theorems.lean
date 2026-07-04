/-
  ActorChannel.Theorems — Six theorems + one impl-fact theorem about the actor/channel model.

  All proved without `sorry`.

  T1  fifo_per_sender           — messages from one sender are received in send order
  T2  closed_no_loss_signal     — try_send fails (never silently drops) on closed;
                                  recv on closed+empty returns immediately (no park)
  T3  close_drains_parked       — close_drain wakes every parked receiver; none left
  T4  actor_sequential          — process_one dispatches at most one message; FIFO preserved
  T5  dispatch_error_no_halt    — a handler error increments error_count, retains
                                  last_error, and does NOT stop further dispatches
  T6  no_lost_task              — a task parked on a channel is either still parked,
                                  woken by a send, or woken by close — never dropped
  T7  bounded_channel_backpressure
                                — full open channel with no waiters cannot grow

  T-fact: legacy_send_closed_noop
                                — channel.spl send() to closed channel enqueues anyway
                                  (the impl has no closed-flag check in send())
-/

import ActorChannel.Basic

namespace ActorChannel

-- Lean 4 needs Inhabited for List.head! on ActorMessage lists.
deriving instance Inhabited for ActorMessage

-- Auxiliary: (a :: t).head! = a — proved by rfl (definitional in Lean 4 stdlib).
private theorem hd_cons {α : Type _} [Inhabited α] (a : α) (t : List α) :
    (a :: t).head! = a := rfl

-- ============================================================
-- § A  T1 — fifo_per_sender
-- ============================================================

/-- Auxiliary: receiving from a non-empty queue returns the head value. -/
theorem recv_returns_head (ch : GreenChannel) (tid : TaskId)
    (hne : ch.queued_values ≠ [])
    : (greenRecv ch tid).value = ch.queued_values.head! := by
  simp [greenRecv, hne]

/-- Auxiliary: after a successful receive the remaining queue is the tail. -/
theorem recv_advances_tail (ch : GreenChannel) (tid : TaskId)
    (hne : ch.queued_values ≠ [])
    : (greenRecv ch tid).channel.queued_values = ch.queued_values.tail := by
  simp [greenRecv, hne]

/-- Auxiliary: receiving a buffered value from an open channel keeps it open. -/
theorem recv_buffered_preserves_open (ch : GreenChannel) (tid : TaskId)
    (hne : ch.queued_values ≠ [])
    (hopen : ch.closed = false)
    : (greenRecv ch tid).channel.closed = false := by
  simp [greenRecv, hne, hopen]

/-- Auxiliary: receiving a buffered value does not park or reorder waiters. -/
theorem recv_buffered_preserves_waiters (ch : GreenChannel) (tid : TaskId)
    (hne : ch.queued_values ≠ [])
    : (greenRecv ch tid).channel.waiting_task_ids = ch.waiting_task_ids := by
  simp [greenRecv, hne]

/-- Auxiliary: receiving a buffered value returns the exact non-parking result. -/
theorem recv_buffered_eq_received_result (ch : GreenChannel) (tid : TaskId)
    (hne : ch.queued_values ≠ []) :
    greenRecv ch tid =
      { channel := { ch with queued_values := ch.queued_values.tail }
      , value := ch.queued_values.head!
      , received := true
      , parked := false
      , channel_closed := false } := by
  simp [greenRecv, hne]

/-- T1 (canonical): Two values sent into a fresh channel (capacity ≥ 2) are received
    in send order.  This is the FIFO-per-sender property: the first message sent is
    the first one received. -/
theorem fifo_per_sender
    (v1 v2 : Val) (cap : Nat) (hcap : cap ≥ 2) :
    let ch : GreenChannel :=
      { capacity := cap, queued_values := [], waiting_task_ids := [], closed := false }
    let r1    := greenSend ch v1
    let r2    := greenSend r1.channel v2
    let recv1 := greenRecv r2.channel 0
    let recv2 := greenRecv recv1.channel 0
    recv1.received = true ∧ recv1.value = v1 ∧
    recv2.received = true ∧ recv2.value = v2 := by
  have h1 : (0 : Nat) < cap := by omega
  have h2 : (1 : Nat) < cap := by omega
  -- After send v1: queue=[v1] (length 1 < cap). After send v2: queue=[v1,v2].
  -- recv1 dequeues v1 (head); recv2 dequeues v2.
  -- Unfold everything and let omega/rfl close numeric and definitional goals.
  simp [greenSend, greenRecv, h1, h2, hd_cons]

-- ============================================================
-- § B  T2 — closed_no_loss_signal
-- ============================================================

/-- T2a: green_channel_send to a closed channel returns channel_closed=true
    and sent=false.  The value is NOT silently dropped — the caller receives
    an explicit failure signal. -/
theorem closed_send_reports_failure (ch : GreenChannel) (v : Val)
    (hclosed : ch.closed = true) :
    let r := greenSend ch v
    r.channel_closed = true ∧ r.sent = false := by
  simp [greenSend, hclosed]

/-- T2a2: green_channel_send to a closed channel leaves channel state unchanged. -/
theorem closed_send_no_mutation (ch : GreenChannel) (v : Val)
    (hclosed : ch.closed = true) :
    (greenSend ch v).channel = ch := by
  simp [greenSend, hclosed]

/-- T2a2a: green_channel_send to a closed channel returns the exact closed
    failure result. -/
theorem closed_send_eq_closed_result (ch : GreenChannel) (v : Val)
    (hclosed : ch.closed = true) :
    greenSend ch v =
      { channel := ch
      , sent := false
      , unparked := false
      , receiver_task_id := 0
      , backpressure := false
      , channel_closed := true } := by
  simp [greenSend, hclosed]

/-- T2a3: green_channel_send to a closed channel keeps it closed. -/
theorem closed_send_preserves_closed (ch : GreenChannel) (v : Val)
    (hclosed : ch.closed = true) :
    (greenSend ch v).channel.closed = true := by
  simp [greenSend, hclosed]

/-- T2b: green_channel_recv on a closed+empty channel returns immediately:
    channel_closed=true, parked=false (no park). -/
theorem closed_empty_recv_no_park (ch : GreenChannel) (tid : TaskId)
    (hclosed : ch.closed = true)
    (hempty  : ch.queued_values = []) :
    let r := greenRecv ch tid
    r.channel_closed = true ∧ r.parked = false := by
  simp [greenRecv, hclosed, hempty]

/-- T2b2: green_channel_recv on a closed+empty channel leaves channel state unchanged. -/
theorem closed_empty_recv_no_mutation (ch : GreenChannel) (tid : TaskId)
    (hclosed : ch.closed = true)
    (hempty  : ch.queued_values = []) :
    (greenRecv ch tid).channel = ch := by
  simp [greenRecv, hclosed, hempty]

/-- T2b2a: green_channel_recv on a closed+empty channel returns the exact
    terminal no-park result. -/
theorem closed_empty_recv_eq_closed_result (ch : GreenChannel) (tid : TaskId)
    (hclosed : ch.closed = true)
    (hempty  : ch.queued_values = []) :
    greenRecv ch tid =
      { channel := ch
      , value := 0
      , received := false
      , parked := false
      , channel_closed := true } := by
  simp [greenRecv, hclosed, hempty]

/-- T2b2b: green_channel_recv on a closed+empty channel keeps it closed. -/
theorem closed_empty_recv_preserves_closed (ch : GreenChannel) (tid : TaskId)
    (hclosed : ch.closed = true)
    (hempty  : ch.queued_values = []) :
    (greenRecv ch tid).channel.closed = true := by
  simp [greenRecv, hclosed, hempty]

/-- T2b3: green_channel_recv on a closed non-empty channel drains a buffered
    value instead of reporting terminal channel_closed. -/
theorem closed_buffered_recv_drains_value
    (ch : GreenChannel) (tid : TaskId) (v : Val) (rest : List Val)
    (hclosed : ch.closed = true)
    (hqueue : ch.queued_values = v :: rest) :
    let r := greenRecv ch tid
    r.received = true ∧
    r.value = v ∧
    r.channel_closed = false ∧
    r.parked = false ∧
    r.channel.queued_values = rest := by
  have hhead : (v :: rest).head! = v := rfl
  simp [greenRecv, hclosed, hqueue, hhead]

/-- T2b4: draining a buffered value from a closed channel keeps it closed. -/
theorem closed_buffered_recv_preserves_closed
    (ch : GreenChannel) (tid : TaskId) (v : Val) (rest : List Val)
    (hclosed : ch.closed = true)
    (hqueue : ch.queued_values = v :: rest) :
    (greenRecv ch tid).channel.closed = true := by
  simp [greenRecv, hclosed, hqueue]

/-- T2c (legacy sync channel): try_send on a closed channel returns false
    and does NOT enqueue the value. -/
theorem legacy_try_send_closed_fails (ch : SyncChannel) (v : Val)
    (hclosed : ch.closed = true) :
    let (ch', ok) := legacyTrySend ch v
    ok = false ∧ ch'.queue = ch.queue := by
  simp [legacyTrySend, hclosed]

-- ============================================================
-- § C  T3 — close_drains_parked
-- ============================================================

/-- T3: green_channel_close_drain wakes every parked receiver.
    After the call: the channel has waiting_task_ids=[], and the
    woken_task_ids list equals the original waiting_task_ids.
    No receiver can remain parked forever on the closed channel. -/
theorem close_drains_parked (ch : GreenChannel) :
    let r := greenCloseDrain ch
    r.channel.waiting_task_ids = [] ∧
    r.woken_task_ids = ch.waiting_task_ids ∧
    r.channel.closed = true := by
  simp [greenCloseDrain]

/-- Corollary: every task that was parked appears in woken_task_ids. -/
theorem close_wakes_all_parked (ch : GreenChannel) (tid : TaskId)
    (hmem : tid ∈ ch.waiting_task_ids) :
    let r := greenCloseDrain ch
    tid ∈ r.woken_task_ids := by
  simp [greenCloseDrain, hmem]

/-- T3a0: close_drain wakes nobody when no receiver is parked. -/
theorem close_drain_no_waiters_no_wake (ch : GreenChannel)
    (hwait : ch.waiting_task_ids = []) :
    (greenCloseDrain ch).woken_task_ids = [] := by
  simp [greenCloseDrain, hwait]

/-- T3a0b: close_drain clears every parked receiver from the channel state. -/
theorem close_drain_clears_waiters (ch : GreenChannel) :
    (greenCloseDrain ch).channel.waiting_task_ids = [] := by
  simp [greenCloseDrain]

/-- T3a0c: close_drain wakes exactly the tasks that were parked. -/
theorem close_drain_woken_eq_waiters (ch : GreenChannel) :
    (greenCloseDrain ch).woken_task_ids = ch.waiting_task_ids := by
  simp [greenCloseDrain]

/-- T3a1: close_drain always leaves the channel closed. -/
theorem close_drain_closes_channel (ch : GreenChannel) :
    (greenCloseDrain ch).channel.closed = true := by
  simp [greenCloseDrain]

/-- T3a2: close_drain wakes waiters but preserves buffered values. -/
theorem close_drain_preserves_buffer (ch : GreenChannel) :
    (greenCloseDrain ch).channel.queued_values = ch.queued_values := by
  simp [greenCloseDrain]

/-- T3a3: buffered values remain receivable after close_drain. -/
theorem close_then_recv_buffered_value
    (ch : GreenChannel) (tid : TaskId) (v : Val) (rest : List Val)
    (hqueue : ch.queued_values = v :: rest) :
    let closed := greenCloseDrain ch
    let recv := greenRecv closed.channel tid
    recv.received = true ∧
    recv.value = v ∧
    recv.parked = false ∧
    recv.channel.queued_values = rest := by
  have hhead : (v :: rest).head! = v := rfl
  simp [greenCloseDrain, greenRecv, hqueue, hhead]

/-- T3b: close_drain is idempotent after the first close: a second close wakes
    no tasks and leaves the already-closed channel unchanged. -/
theorem close_drain_idempotent_after_close (ch : GreenChannel) :
    let first := greenCloseDrain ch
    let second := greenCloseDrain first.channel
    second.channel = first.channel ∧ second.woken_task_ids = [] := by
  simp [greenCloseDrain]

-- ============================================================
-- § D  T4 — actor_sequential
-- ============================================================

/-- T4a: process_one dispatches at most one message (mailbox length non-increasing). -/
theorem process_one_at_most_one (ht : HandlerTable) (s : ActorState) :
    let (s', _) := processOne ht s
    s'.mailbox.length ≤ s.mailbox.length := by
  simp only [processOne]
  split
  · -- not alive: unchanged
    simp
  · split
    · -- empty mailbox: unchanged
      simp
    · -- msg :: t case: after dispatch, mailbox = t, length = s.mailbox.length - 1
      rename_i msg t _halive _hempty
      -- The inner `if r.isOk` split produces two states, both with mailbox = t
      -- Goal: _halive.length ≤ s.mailbox.length; rewrite s.mailbox via _hempty
      split <;> (rw [_hempty]; simp [List.length_cons])

/-- T4b: FIFO ordering preserved — after process_one the remaining mailbox
    is exactly the tail of the original. -/
theorem process_one_preserves_fifo (ht : HandlerTable) (s : ActorState)
    (halive : s.alive = true)
    (hne    : s.mailbox ≠ []) :
    let (s', _) := processOne ht s
    s'.mailbox = s.mailbox.tail := by
  unfold processOne
  rw [show (!s.alive) = false from by simp [halive]]
  match h : s.mailbox with
  | []       => exact absurd h hne
  | msg :: t =>
    simp only [List.tail_cons]
    -- The unfolded term still has a residual split on `!s.alive`.
    -- isTrue branch: h✝ : false = true → contradiction.
    -- isFalse branch: the real dispatch; both ok and error leave mailbox = t.
    split
    · contradiction
    · split <;> simp

-- ============================================================
-- § E  T5 — dispatch_error_no_halt
-- ============================================================

/-- T5: A handler error increments error_count by exactly 1, updates last_error,
    and does NOT prevent subsequent dispatches (actor remains alive, mailbox advanced). -/
theorem dispatch_error_no_halt (ht : HandlerTable) (s : ActorState)
    (halive : s.alive = true)
    (hne    : s.mailbox ≠ [])
    (herr   : (dispatchMsg ht s.mailbox.head!).isOk = false) :
    let (s', _) := processOne ht s
    s'.error_count = s.error_count + 1 ∧
    s'.alive = true ∧
    s'.mailbox = s.mailbox.tail ∧
    s'.last_error = (dispatchMsg ht s.mailbox.head!).error_msg := by
  unfold processOne
  rw [show (!s.alive) = false from by simp [halive]]
  match h : s.mailbox with
  | []       => exact absurd h hne
  | msg :: t =>
    -- Rewrite head! in herr: s.mailbox = msg :: t, so s.mailbox.head! = msg
    have hhead : s.mailbox.head! = msg := h ▸ hd_cons msg t
    rw [hhead] at herr
    simp only [List.tail_cons]
    simp only [DispatchResult.isOk] at herr
    -- The residual `!s.alive` split
    split
    · contradiction
    · -- real dispatch on msg
      split
      · -- isOk = true: but herr says status ≠ Ok → contradiction
        rename_i hok
        simp only [DispatchResult.isOk] at hok
        simp [herr] at hok
      · -- isOk = false: our case
        -- last_error goal: .last_error = (dispatchMsg ht (msg::t).head!).error_msg
        -- (msg::t).head! = msg definitionally, so rfl closes it
        exact ⟨rfl, halive, rfl, rfl⟩

/-- T5 scheduler variant: runOnce increments total_errors on handler error
    and returns more=true (not halted). -/
theorem scheduler_error_no_halt (ht : HandlerTable) (ss : SchedulerState)
    (halive : ss.actorState.alive = true)
    (hne    : ss.actorState.mailbox ≠ [])
    (herr   : (dispatchMsg ht ss.actorState.mailbox.head!).isOk = false) :
    let (ss', more) := runOnce ht ss
    ss'.total_errors = ss.total_errors + 1 ∧
    more = true ∧
    ss'.actorState.alive = true := by
  unfold runOnce processOne
  rw [show (!ss.actorState.alive) = false from by simp [halive]]
  match h : ss.actorState.mailbox with
  | []       => exact absurd h hne
  | msg :: t =>
    have hhead : ss.actorState.mailbox.head! = msg := h ▸ hd_cons msg t
    rw [hhead] at herr
    -- herr : (dispatchMsg ht msg).isOk = false
    have hnotok : (dispatchMsg ht msg).isOk = false := herr
    -- Use full simp to reduce the match on rOpt and the nested ite
    simp [hnotok, halive]

/-- A dead actor has no runnable work: runOnce leaves scheduler state unchanged. -/
theorem scheduler_dead_actor_no_dispatch (ht : HandlerTable) (ss : SchedulerState)
    (hdead : ss.actorState.alive = false) :
    runOnce ht ss = (ss, false) := by
  simp [runOnce, processOne, hdead]

/-- An alive actor with an empty mailbox has no runnable work: runOnce is idle. -/
theorem scheduler_empty_mailbox_no_dispatch (ht : HandlerTable) (ss : SchedulerState)
    (halive : ss.actorState.alive = true)
    (hempty : ss.actorState.mailbox = []) :
    runOnce ht ss = (ss, false) := by
  simp [runOnce, processOne, halive, hempty]

/-- T5b: A handler error on one scheduler tick does not starve the next queued
    successful message; the next run_once still dispatches it. -/
theorem scheduler_error_then_next_ok_dispatches
    (ht : HandlerTable) (ss : SchedulerState)
    (msg1 msg2 : ActorMessage) (rest : List ActorMessage)
    (halive : ss.actorState.alive = true)
    (hmail : ss.actorState.mailbox = msg1 :: msg2 :: rest)
    (herr : (dispatchMsg ht msg1).isOk = false)
    (hok : (dispatchMsg ht msg2).isOk = true) :
    let first := runOnce ht ss
    let second := runOnce ht first.1
    second.1.total_errors = ss.total_errors + 1 ∧
    second.1.total_dispatched = ss.total_dispatched + 1 ∧
    second.1.actorState.mailbox = rest ∧
    second.1.actorState.alive = true ∧
    second.2 = true := by
  simp [runOnce, processOne, halive, hmail, herr, hok]

theorem scheduler_two_ok_messages_dispatch_in_two_ticks
    (ht : HandlerTable) (ss : SchedulerState)
    (msg1 msg2 : ActorMessage) (rest : List ActorMessage)
    (halive : ss.actorState.alive = true)
    (hmail : ss.actorState.mailbox = msg1 :: msg2 :: rest)
    (hok1 : (dispatchMsg ht msg1).isOk = true)
    (hok2 : (dispatchMsg ht msg2).isOk = true) :
    let first := runOnce ht ss
    let second := runOnce ht first.1
    second.1.total_dispatched = ss.total_dispatched + 2 ∧
    second.1.total_errors = ss.total_errors ∧
    second.1.actorState.mailbox = rest ∧
    second.1.actorState.alive = true ∧
    first.2 = true ∧
    second.2 = true := by
  simp [runOnce, processOne, halive, hmail, hok1, hok2]

-- ============================================================
-- § F  T6 — no_lost_task
-- ============================================================

/-- T6a: A task in waiting_task_ids after a send is either still waiting
    or was unparked (received as receiver_task_id).

    After the send: the head waiter is removed (unparked) and the tail remains.
    Since tid was in the list, it is either the head (unparked) or in the tail. -/
theorem no_lost_task_send (ch : GreenChannel) (v : Val) (tid : TaskId)
    (hmem    : tid ∈ ch.waiting_task_ids)
    (hopen   : ch.closed = false)
    (hwaiter : ch.waiting_task_ids ≠ []) :
    let r := greenSend ch v
    tid ∈ r.channel.waiting_task_ids ∨ (r.unparked = true ∧ r.receiver_task_id = tid) := by
  simp only [greenSend, hopen]
  cases h : ch.waiting_task_ids with
  | nil  => exact absurd h hwaiter
  | cons hd tl =>
    -- head! = hd by rfl; tail = tl
    show tid ∈ tl ∨ (true = true ∧ hd = tid)
    by_cases htid : tid = hd
    · right
      -- receiver_task_id = (hd :: tl).head! = hd; htid : tid = hd, so hd = tid
      exact ⟨rfl, (show (hd :: tl).head! = hd from rfl).trans htid.symm⟩
    · left
      have hmem' : tid ∈ tl := by
        have hmem2 := List.mem_cons.mp (h ▸ hmem)
        exact hmem2.resolve_left htid
      exact hmem'

/-- T6b: A task in waiting_task_ids appears in woken_task_ids after close_drain. -/
theorem no_lost_task_close (ch : GreenChannel) (tid : TaskId)
    (hmem : tid ∈ ch.waiting_task_ids) :
    let r := greenCloseDrain ch
    tid ∈ r.woken_task_ids := by
  simp [greenCloseDrain, hmem]

/-- T6c: When recv parks a task, that task appears in waiting_task_ids. -/
theorem no_lost_task_recv_parks (ch : GreenChannel) (tid : TaskId)
    (hempty  : ch.queued_values = [])
    (hopen   : ch.closed = false) :
    let r := greenRecv ch tid
    tid ∈ r.channel.waiting_task_ids := by
  simp [greenRecv, hempty, hopen]

/-- T6c1: recv on an open empty channel returns the exact parked result. -/
theorem recv_open_empty_eq_parked_result (ch : GreenChannel) (tid : TaskId)
    (hempty  : ch.queued_values = [])
    (hopen   : ch.closed = false) :
    greenRecv ch tid =
      { channel := { ch with waiting_task_ids := ch.waiting_task_ids ++ [tid] }
      , value := 0
      , received := false
      , parked := true
      , channel_closed := false } := by
  simp [greenRecv, hempty, hopen]

/-- T6c2: Parking a receiver on an open empty channel keeps it open. -/
theorem recv_parks_preserves_open (ch : GreenChannel) (tid : TaskId)
    (hempty  : ch.queued_values = [])
    (hopen   : ch.closed = false) :
    (greenRecv ch tid).channel.closed = false := by
  simp [greenRecv, hempty, hopen]

/-- T6d: A receiver parked by recv is woken by a later close_drain, and the
    closed channel has no remaining parked receivers. -/
theorem recv_then_close_wakes_parked (ch : GreenChannel) (tid : TaskId)
    (hempty  : ch.queued_values = [])
    (hopen   : ch.closed = false) :
    let recv := greenRecv ch tid
    let closed := greenCloseDrain recv.channel
    tid ∈ closed.woken_task_ids ∧ closed.channel.waiting_task_ids = [] := by
  simp [greenRecv, greenCloseDrain, hempty, hopen]

/-- T6d1: Closing after recv parks a receiver wakes exactly the previous
    waiters plus the newly parked receiver, with no waiter left behind. -/
theorem recv_then_close_exact_woken_waiters (ch : GreenChannel) (tid : TaskId)
    (hempty  : ch.queued_values = [])
    (hopen   : ch.closed = false) :
    let recv := greenRecv ch tid
    let closed := greenCloseDrain recv.channel
    closed.woken_task_ids = ch.waiting_task_ids ++ [tid] ∧
    closed.channel.waiting_task_ids = [] := by
  simp [greenRecv, greenCloseDrain, hempty, hopen]

/-- T6e: Sending to a channel with a waiting receiver wakes the head waiter
    directly and does not grow the buffered queue. -/
theorem send_to_waiter_wakes_without_buffer_growth
    (ch : GreenChannel) (v : Val) (tid : TaskId) (rest : List TaskId)
    (hopen : ch.closed = false)
    (hwait : ch.waiting_task_ids = tid :: rest) :
    let r := greenSend ch v
    r.sent = true ∧
    r.unparked = true ∧
    r.receiver_task_id = tid ∧
    r.channel.waiting_task_ids = rest ∧
    r.channel.queued_values = ch.queued_values := by
  have hhead : (tid :: rest).head! = tid := rfl
  simp [greenSend, hopen, hwait, hhead]

/-- T6e1: Sending to a waiting receiver returns the exact wake result. -/
theorem send_to_waiter_eq_wake_result
    (ch : GreenChannel) (v : Val) (tid : TaskId) (rest : List TaskId)
    (hopen : ch.closed = false)
    (hwait : ch.waiting_task_ids = tid :: rest) :
    greenSend ch v =
      { channel := { ch with waiting_task_ids := rest }
      , sent := true
      , unparked := true
      , receiver_task_id := tid
      , backpressure := false
      , channel_closed := false } := by
  have hhead : (tid :: rest).head! = tid := rfl
  simp [greenSend, hopen, hwait, hhead]

/-- T6f: Sending to a waiting receiver on an open channel keeps it open. -/
theorem send_to_waiter_preserves_open
    (ch : GreenChannel) (v : Val) (tid : TaskId) (rest : List TaskId)
    (hopen : ch.closed = false)
    (hwait : ch.waiting_task_ids = tid :: rest) :
    (greenSend ch v).channel.closed = false := by
  have hhead : (tid :: rest).head! = tid := rfl
  simp [greenSend, hopen, hwait, hhead]

/-- T6f1: A waiting receiver takes priority over backpressure even when the
    buffer is full; the send wakes the waiter and does not alter the buffer. -/
theorem send_to_waiter_beats_full_buffer
    (ch : GreenChannel) (v : Val) (tid : TaskId) (rest : List TaskId)
    (hopen : ch.closed = false)
    (hwait : ch.waiting_task_ids = tid :: rest)
    (_hfull : ch.capacity ≤ ch.queued_values.length) :
    let r := greenSend ch v
    r.sent = true ∧
    r.unparked = true ∧
    r.backpressure = false ∧
    r.channel.queued_values = ch.queued_values := by
  have hhead : (tid :: rest).head! = tid := rfl
  simp [greenSend, hopen, hwait, hhead]

/-- T6g: Buffering a value on an open channel keeps it open. -/
theorem send_buffered_preserves_open
    (ch : GreenChannel) (v : Val)
    (hopen : ch.closed = false)
    (hwait : ch.waiting_task_ids = [])
    (hroom : ch.queued_values.length < ch.capacity) :
    (greenSend ch v).channel.closed = false := by
  have hnot_wait : ¬ ch.waiting_task_ids ≠ [] := by simp [hwait]
  simp [greenSend, hopen, hnot_wait, hroom]

/-- T6g1: Sending to open buffer capacity returns the exact buffered result. -/
theorem send_buffered_eq_sent_result
    (ch : GreenChannel) (v : Val)
    (hopen : ch.closed = false)
    (hwait : ch.waiting_task_ids = [])
    (hroom : ch.queued_values.length < ch.capacity) :
    greenSend ch v =
      { channel := { ch with queued_values := ch.queued_values ++ [v] }
      , sent := true
      , unparked := false
      , receiver_task_id := 0
      , backpressure := false
      , channel_closed := false } := by
  have hnot_wait : ¬ ch.waiting_task_ids ≠ [] := by simp [hwait]
  simp [greenSend, hopen, hnot_wait, hroom]

-- ============================================================
-- § G  T7 — bounded channel backpressure
-- ============================================================

/-- T7: A full, open channel with no waiting receiver reports backpressure and
    leaves the channel unchanged.  This is the bounded-buffer race/resource
    invariant: send cannot overflow capacity when producers outrun consumers. -/
theorem bounded_channel_backpressure_no_overflow
    (ch : GreenChannel) (v : Val)
    (hopen : ch.closed = false)
    (hwait : ch.waiting_task_ids = [])
    (hfull : ch.capacity ≤ ch.queued_values.length) :
    let r := greenSend ch v
    r.backpressure = true ∧ r.sent = false ∧ r.channel = ch := by
  have hnot_wait : ¬ ch.waiting_task_ids ≠ [] := by simp [hwait]
  have hnot_room : ¬ ch.queued_values.length < ch.capacity := by omega
  simp [greenSend, hopen, hnot_wait, hnot_room]

/-- T7b: Backpressure on an open full channel keeps it open. -/
theorem bounded_channel_backpressure_preserves_open
    (ch : GreenChannel) (v : Val)
    (hopen : ch.closed = false)
    (hwait : ch.waiting_task_ids = [])
    (hfull : ch.capacity ≤ ch.queued_values.length) :
    (greenSend ch v).channel.closed = false := by
  have hnot_wait : ¬ ch.waiting_task_ids ≠ [] := by simp [hwait]
  have hnot_room : ¬ ch.queued_values.length < ch.capacity := by omega
  simp [greenSend, hopen, hnot_wait, hnot_room]

-- ============================================================
-- § H  T-fact: legacy_send_closed_noop
-- ============================================================

/-- Fact (not a violation): channel.spl's `send()` has no closed-flag check.
    It delegates directly to rt_channel_send, which enqueues unconditionally.
    Only `try_send` checks the closed flag.

    Source note: channel.spl comment says "If channel is closed, send is
    silently ignored" — this describes the *runtime* behaviour of the Rust
    rt_channel_send FFI, not a check in the Simple layer.  The Simple `send`
    function has no explicit guard.

    This is a KNOWN CONTRACT of the legacy sync channel.  The green channel
    (green_channel.spl) corrects this: green_channel_send explicitly returns
    channel_closed=true on a closed channel (T2a above). -/
theorem legacy_send_closed_noop (ch : SyncChannel) (v : Val)
    (hclosed : ch.closed = true) :
    -- legacySend always enqueues regardless of the closed flag
    (legacySend ch v).queue = ch.queue ++ [v] ∧
    (legacySend ch v).closed = true := by
  simp [legacySend, hclosed]

/-- Contrast: try_send on the same closed channel does NOT enqueue. -/
theorem legacy_try_send_closed_no_enqueue (ch : SyncChannel) (v : Val)
    (hclosed : ch.closed = true) :
    (legacyTrySend ch v).1.queue = ch.queue := by
  simp [legacyTrySend, hclosed]

/-- Legacy recv on a non-empty sync channel returns the head and advances
    the queue by exactly one element. -/
theorem legacy_recv_nonempty_dequeues_head (ch : SyncChannel) (v : Val) (rest : List Val)
    (hqueue : ch.queue = v :: rest) :
    legacyRecv ch = ({ ch with queue := rest }, some v) := by
  simp [legacyRecv, hqueue]

end ActorChannel
