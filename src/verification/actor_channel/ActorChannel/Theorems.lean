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

/-- T2b: green_channel_recv on a closed+empty channel returns immediately:
    channel_closed=true, parked=false (no park). -/
theorem closed_empty_recv_no_park (ch : GreenChannel) (tid : TaskId)
    (hclosed : ch.closed = true)
    (hempty  : ch.queued_values = []) :
    let r := greenRecv ch tid
    r.channel_closed = true ∧ r.parked = false := by
  simp [greenRecv, hclosed, hempty]

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
    simp only [h, List.tail_cons]
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
    simp only [h, List.tail_cons]
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
    simp [h, hnotok, halive]

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
  simp only [greenSend, hopen, hwaiter, decide_eq_false_iff_not,
             not_false_eq_true, ite_true, ite_false]
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

-- ============================================================
-- § G  T-fact: legacy_send_closed_noop
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

end ActorChannel
