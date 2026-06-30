/-
  KernelScheduler.Basic — Lean 4 formal model of the SimpleOS kernel green-task
  scheduler.

  Wave 3b; plan: doc/03_plan/runtime/hardening_formal_verification_2026-06-11.md

  Source of truth:
    src/os/kernel/scheduler/green_task.spl    (GreenTaskRecord, lifecycle fns)
    src/os/kernel/scheduler/green_worker.spl  (GreenWorkerPlacement, placement fns)

  Design
  ======
  The model is a pure-functional state machine.  Every transition function is
  *pure*: it takes the old state and returns a new state plus a result record,
  exactly as the Simple source does.  No closures are modelled; "running" a task
  is abstracted as the transition runnable → done (or runnable → parked).

  IMPLEMENTATION FACTS (not violations):
  ──────────────────────────────────────
  1. green_task.spl has exactly three task states: "runnable", "parked", "done".
     There is no separate "running" or "error" state in the source.
  2. green_task_unpark called on a NON-parked task returns should_enqueue=false
     and leaves the task unchanged.  This is the correct guard; a duplicate
     unpark is a silent no-op.
  3. green_worker_cpu_allowed: affinity_mask == 0 means ALL CPUs allowed
     (except negative indices, which are unconditionally denied).
  4. The scheduler has no run-until-idle loop in green_task.spl or
     green_worker.spl — those files are pure placement-logic helpers used by
     the future SimpleOS carrier bridge.  "Running all tasks" is therefore
     modelled as a fold over a ready queue (see `runBatch`), not as an
     interpreter loop.

  FINDING-T1: CLOSED — double-complete guard added to source
  ────────────────────────────────────────────────────────────
  green_task_complete in green_task.spl now checks `task.state == GREEN_TASK_DONE`
  at entry; if the task is already done the call is a no-op and the first result
  is preserved (first-write-wins).  GreenTask.complete below models this guard.
  T5b in Theorems.lean is upgraded to prove full double-complete safety: a second
  complete with ANY result is identity.
-/

namespace KernelScheduler

-- ============================================================
-- § 1  Task state tags
-- ============================================================

/-- The three lifecycle states of a SimpleOS green task.
    Mirrors GREEN_TASK_RUNNABLE / GREEN_TASK_PARKED / GREEN_TASK_DONE in
    green_task.spl. -/
inductive TaskState where
  | runnable : TaskState
  | parked   : TaskState
  | done     : TaskState
  deriving DecidableEq, Repr, Inhabited

-- ============================================================
-- § 2  GreenTask record
-- ============================================================

/-- Pure-functional state of a logical green task.
    Mirrors GreenTaskRecord in green_task.spl field-for-field.
      task_id      : opaque unique identifier
      home_cpu     : CPU chosen at spawn; stable across park/unpark
      assigned_cpu : current run-queue CPU; may change on unpark
      affinity_mask: 0 = any CPU, non-zero = bitmask of allowed CPUs
      state        : runnable | parked | done
      park_reason  : non-empty only when state = parked
      result_val   : set by complete -/
structure GreenTask where
  task_id      : Nat
  home_cpu     : Nat
  assigned_cpu : Nat
  affinity_mask : Nat   -- 0 = unrestricted
  state        : TaskState
  park_reason  : String
  result_val   : Int
  deriving Repr, Inhabited

-- ============================================================
-- § 3  GreenWorkerPlacement
-- ============================================================

/-- CPU placement decision.  Mirrors GreenWorkerPlacement in green_worker.spl. -/
structure WorkerPlacement where
  cpu    : Nat
  reason : String
  deriving Repr

-- ============================================================
-- § 4  Wake decision
-- ============================================================

/-- Wake decision returned by unpark.
    Mirrors GreenTaskWakeDecision in green_task.spl. -/
structure WakeDecision where
  task          : GreenTask
  placement     : WorkerPlacement
  should_enqueue : Bool
  deriving Repr

-- ============================================================
-- § 5  Task transition functions
-- ============================================================

/-- Create a new runnable task on the given CPU.
    Mirrors green_task_new — CPU selection is abstracted; caller supplies cpu. -/
def GreenTask.new (task_id home_cpu : Nat) (affinity_mask : Nat) : GreenTask :=
  { task_id      := task_id
  , home_cpu     := home_cpu
  , assigned_cpu := home_cpu
  , affinity_mask := affinity_mask
  , state        := .runnable
  , park_reason  := ""
  , result_val   := 0 }

/-- Park a runnable green task.
    Mirrors green_task_park.  Home and assigned CPU are preserved. -/
def GreenTask.park (t : GreenTask) (reason : String) : GreenTask :=
  { t with state := .parked, park_reason := reason }

/-- Unpark a parked green task.
    Mirrors green_task_unpark.
    If the task is already non-parked, returns should_enqueue=false unchanged. -/
def GreenTask.unpark (t : GreenTask) (waker_cpu : Nat) : WakeDecision :=
  if t.state = .parked then
    { task          := { t with state := .runnable
                              , assigned_cpu := waker_cpu
                              , park_reason := "" }
    , placement     := { cpu := waker_cpu, reason := "wake_affine_waker_cpu" }
    , should_enqueue := true }
  else
    { task          := t
    , placement     := { cpu := t.assigned_cpu, reason := "not_parked" }
    , should_enqueue := false }

/-- Complete a green task.
    Mirrors green_task_complete (with the FINDING-T1 guard now in source).
    First-write-wins: if the task is already done, return it unchanged.
    Assigned CPU is preserved on the first completion. -/
def GreenTask.complete (t : GreenTask) (result : Int) : GreenTask :=
  if t.state = .done then t
  else { t with state := .done, result_val := result }

-- ============================================================
-- § 6  CPU affinity helper
-- ============================================================

/-- cpu_allowed (affinity_mask cpu): true iff the CPU is permitted by the mask.
    Mirrors green_worker_cpu_allowed in green_worker.spl.
    mask = 0 means unrestricted; mask ≠ 0 means the bit must be set. -/
def cpuAllowed (mask cpu : Nat) : Bool :=
  mask = 0 || (mask &&& (1 <<< cpu)) ≠ 0

-- ============================================================
-- § 7  Work-steal threshold helper
-- ============================================================

/-- should_steal (local_load remote_load threshold): steal when
    remote − local > threshold.
    Mirrors green_worker_should_steal in green_worker.spl. -/
def shouldSteal (local_load remote_load threshold : Nat) : Bool :=
  remote_load > local_load + threshold

-- ============================================================
-- § 8  Scheduler state (ready queue abstraction)
-- ============================================================

/-- A minimal scheduler state: a ready queue of runnable tasks. -/
structure SchedState where
  ready : List GreenTask
  deriving Repr

/-- Enqueue a runnable task.  Mirrors the carrier bridge's enqueue operation. -/
def SchedState.enqueue (s : SchedState) (t : GreenTask) : SchedState :=
  { s with ready := s.ready ++ [t] }

/-- Step: pop the head task from the ready queue.
    Returns (Some task, new_state) or (none, unchanged) if empty. -/
def SchedState.popHead (s : SchedState) : Option GreenTask × SchedState :=
  match s.ready with
  | []     => (none, s)
  | t :: rest => (some t, { s with ready := rest })

/-- Run one task: pop from queue, mark as done.
    If queue is empty, returns state unchanged. -/
def SchedState.runOne (s : SchedState) : SchedState :=
  match s.popHead with
  | (none, s')   => s'
  | (some _, s') => s'  -- task is "run"; result absorbed; state = done (not re-queued)

/-- Run all ready tasks until the queue is empty.
    Terminates because each step strictly decrements the queue length. -/
def SchedState.runBatch : SchedState → SchedState
  | { ready := [] }   => { ready := [] }
  | { ready := _ :: rest } => SchedState.runBatch { ready := rest }

end KernelScheduler
