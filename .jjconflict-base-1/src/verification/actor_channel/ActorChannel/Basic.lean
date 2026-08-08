/-
  ActorChannel.Basic — Lean 4 formal model of Simple's actor/channel/green-thread semantics.

  Wave 3b; plan: doc/03_plan/runtime/hardening_formal_verification_2026-06-11.md

  Source of truth:
    src/lib/nogc_sync_mut/concurrent/channel.spl          (legacy sync channel)
    src/lib/nogc_async_mut/concurrent/green_channel.spl   (green channel — pure functional LTS)
    src/lib/nogc_async_mut/concurrent/green_thread.spl    (green thread scheduler)
    src/lib/nogc_async_mut/actor/actor.spl                (Actor / DispatchResult)
    src/lib/nogc_async_mut/actor/scheduler.spl            (ActorScheduler.run_once)

  Design
  ======
  The model is a labelled transition system (LTS).  Every "step" function is
  *pure*: it takes the old state and returns a new state plus a result record,
  exactly as the Simple source does.  Theorems are proved by structural
  induction / case analysis on the resulting state.

  IMPLEMENTATION FACTS (not violations):
  ──────────────────────────────────────
  1. channel.spl `send()` to a closed channel is a **silent no-op** (backed by
     `rt_channel_send`; the closed flag check is NOT in `send`, only in
     `try_send`).  This is modelled as `legacy_send_closed_noop` (T-fact).
  2. `green_channel_send` to a closed channel returns `sent=false,
     channel_closed=true` — a reporting failure, not a silent drop.
  3. `green_channel_recv` on a closed+empty channel returns immediately with
     `channel_closed=true, parked=false` — no park.
  4. `green_channel_close_drain` drains `waiting_task_ids` into `woken_task_ids`.
-/

namespace ActorChannel

-- ============================================================
-- § 1  Task IDs and values (opaque Nat)
-- ============================================================

/-- A green task identifier.  Modelled as a natural number. -/
abbrev TaskId := Nat

/-- A channel value.  Modelled as a natural number (i64 in impl). -/
abbrev Val := Nat

-- ============================================================
-- § 2  GreenChannel state
-- ============================================================

/-- Pure-functional state of a green channel.
    Matches `GreenChannel` in green_channel.spl field-for-field:
      capacity        : positive bound (normalised to ≥ 1)
      queued_values   : FIFO queue of buffered values (head = oldest)
      waiting_task_ids: ordered list of parked receivers (head = next to wake)
      closed          : set by close / close_drain
-/
structure GreenChannel where
  capacity        : Nat
  queued_values   : List Val
  waiting_task_ids : List TaskId
  closed          : Bool
  deriving Repr

/-- Well-formedness: capacity ≥ 1, and a closed channel has no parked receivers
    (the impl drains them immediately in close_drain). -/
def GreenChannel.wf (ch : GreenChannel) : Prop :=
  ch.capacity ≥ 1 ∧
  (ch.closed → ch.waiting_task_ids = [])

def GreenChannel.new (cap : Nat) : GreenChannel :=
  { capacity        := if cap < 1 then 1 else cap
  , queued_values   := []
  , waiting_task_ids := []
  , closed          := false }

-- ============================================================
-- § 3  GreenChannel transition results
-- ============================================================

/-- Result of `green_channel_send`. -/
structure SendResult where
  channel        : GreenChannel
  sent           : Bool
  unparked       : Bool
  receiver_task_id : TaskId      -- meaningful iff unparked = true
  backpressure   : Bool
  channel_closed : Bool
  deriving Repr

/-- Result of `green_channel_recv`. -/
structure RecvResult where
  channel        : GreenChannel
  value          : Val           -- meaningful iff received = true
  received       : Bool
  parked         : Bool
  channel_closed : Bool
  deriving Repr

/-- Result of `green_channel_close_drain`. -/
structure CloseResult where
  channel        : GreenChannel
  woken_task_ids : List TaskId
  deriving Repr

-- ============================================================
-- § 4  GreenChannel transition functions
-- (pure model; mirror green_channel.spl exactly)
-- ============================================================

/-- Send one value.
    Closed → channel_closed=true, sent=false (NOT a silent drop).
    Has waiter → unpark head waiter, sent=true.
    Has capacity → buffer, sent=true.
    Full → backpressure, sent=false. -/
def greenSend (ch : GreenChannel) (v : Val) : SendResult :=
  if ch.closed then
    { channel := ch, sent := false, unparked := false
    , receiver_task_id := 0, backpressure := false, channel_closed := true }
  else if ch.waiting_task_ids ≠ [] then
    let tid := ch.waiting_task_ids.head!
    { channel := { ch with waiting_task_ids := ch.waiting_task_ids.tail }
    , sent := true, unparked := true, receiver_task_id := tid
    , backpressure := false, channel_closed := false }
  else if ch.queued_values.length < ch.capacity then
    { channel := { ch with queued_values := ch.queued_values ++ [v] }
    , sent := true, unparked := false, receiver_task_id := 0
    , backpressure := false, channel_closed := false }
  else
    { channel := ch, sent := false, unparked := false
    , receiver_task_id := 0, backpressure := true, channel_closed := false }

/-- Receive one value or park.
    Has buffered value → dequeue head, received=true.
    Closed+empty → channel_closed=true, parked=false (no park).
    Open+empty → park task_id, parked=true. -/
def greenRecv (ch : GreenChannel) (tid : TaskId) : RecvResult :=
  if ch.queued_values ≠ [] then
    { channel := { ch with queued_values := ch.queued_values.tail }
    , value := ch.queued_values.head!, received := true
    , parked := false, channel_closed := false }
  else if ch.closed then
    { channel := ch, value := 0, received := false
    , parked := false, channel_closed := true }
  else
    { channel := { ch with waiting_task_ids := ch.waiting_task_ids ++ [tid] }
    , value := 0, received := false, parked := true, channel_closed := false }

/-- Close and drain parked receivers.
    Returns closed channel (waiting_task_ids=[]) + list of woken task IDs. -/
def greenCloseDrain (ch : GreenChannel) : CloseResult :=
  { channel        := { ch with waiting_task_ids := [], closed := true }
  , woken_task_ids := ch.waiting_task_ids }

-- ============================================================
-- § 5  Legacy sync-channel model (channel.spl)
-- ============================================================

/-- Minimal model of the legacy sync channel.
    The `send` method does NOT check the closed flag — it always enqueues.
    `try_send` checks the flag and returns false if closed. -/
structure SyncChannel where
  queue  : List Val
  closed : Bool
  deriving Repr

/-- Legacy send: always enqueues even when closed (rt_channel_send is unconditional). -/
def legacySend (ch : SyncChannel) (v : Val) : SyncChannel :=
  { ch with queue := ch.queue ++ [v] }

/-- try_send: checks closed first; returns (new_channel, success). -/
def legacyTrySend (ch : SyncChannel) (v : Val) : SyncChannel × Bool :=
  if ch.closed then (ch, false)
  else ({ ch with queue := ch.queue ++ [v] }, true)

/-- recv: returns head of queue (Some v) or none when empty.
    On closed+empty channel the impl returns nil. -/
def legacyRecv (ch : SyncChannel) : SyncChannel × Option Val :=
  match ch.queue with
  | []      => (ch, none)
  | v :: t  => ({ ch with queue := t }, some v)

-- ============================================================
-- § 6  Actor / Mailbox model
-- ============================================================

/-- A message: a method name (opaque Nat) + argument list (opaque list of Nat). -/
structure ActorMessage where
  method  : Nat
  args    : List Nat
  reply_id : Option Nat
  deriving Repr

/-- Dispatch result: ok with a value, or an error with a message. -/
inductive DispatchStatus where
  | Ok
  | MethodNotFound
  | HandlerError
  deriving DecidableEq, Repr

structure DispatchResult where
  status    : DispatchStatus
  value     : Nat   -- meaningful iff status = Ok
  error_msg : Nat   -- opaque error id; 0 = none
  deriving Repr

def DispatchResult.isOk (r : DispatchResult) : Bool :=
  r.status == DispatchStatus.Ok

/-- An actor's mutable state (the fields that change during dispatch). -/
structure ActorState where
  mailbox         : List ActorMessage   -- FIFO; head = next to dispatch
  processed_count : Nat
  error_count     : Nat
  last_error      : Nat   -- 0 = no error
  alive           : Bool
  deriving Repr

/-- Handler table: a partial function from method id to a result.
    We abstract over the actual handler body. -/
abbrev HandlerTable := Nat → Option DispatchResult

/-- Dispatch one message via handler table. -/
def dispatchMsg (ht : HandlerTable) (msg : ActorMessage) : DispatchResult :=
  match ht msg.method with
  | some r => r
  | none   => { status := DispatchStatus.MethodNotFound, value := 0, error_msg := msg.method }

/-- process_one: dequeue head message, dispatch, update counts.
    Returns (new_state, result option).
    If mailbox empty or actor not alive → returns (state, none). -/
def processOne (ht : HandlerTable) (s : ActorState) : ActorState × Option DispatchResult :=
  if !s.alive then (s, none)
  else match s.mailbox with
  | []       => (s, none)
  | msg :: t =>
    let r := dispatchMsg ht msg
    let s' :=
      if r.isOk then
        { s with mailbox := t, processed_count := s.processed_count + 1 }
      else
        { s with mailbox := t, error_count := s.error_count + 1
               , last_error := r.error_msg }
    (s', some r)

-- ============================================================
-- § 7  Scheduler model
-- ============================================================

/-- A minimal single-actor scheduler state (enough to state T5). -/
structure SchedulerState where
  actorState      : ActorState
  total_dispatched : Nat
  total_errors    : Nat
  deriving Repr

/-- run_once: mirrors ActorScheduler.run_once for a single actor.
    On error: increments error_count + last_error; does NOT stop. -/
def runOnce (ht : HandlerTable) (ss : SchedulerState) : SchedulerState × Bool :=
  let (s', rOpt) := processOne ht ss.actorState
  match rOpt with
  | none   => ({ ss with actorState := s' }, false)
  | some r =>
    if r.isOk then
      ({ ss with actorState := s', total_dispatched := ss.total_dispatched + 1 }, true)
    else
      ({ ss with actorState := s', total_errors := ss.total_errors + 1 }, true)

end ActorChannel
