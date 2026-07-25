/-
  KernelScheduler.Theorems — Lean 4 proofs for the SimpleOS kernel green-task
  scheduler model.

  Wave 3b; plan: doc/03_plan/runtime/hardening_formal_verification_2026-06-11.md

  SOURCE FIDELITY MAP
  ═══════════════════
  Lean symbol              ↔  Simple source function / field
  ─────────────────────────────────────────────────────────────────────────────
  GreenTask.new            ↔  green_task_new (green_task.spl)
  GreenTask.park           ↔  green_task_park
  GreenTask.unpark         ↔  green_task_unpark
  GreenTask.complete       ↔  green_task_complete
  cpuAllowed               ↔  green_worker_cpu_allowed (green_worker.spl)
  shouldSteal              ↔  green_worker_should_steal
  SchedState.enqueue       ↔  carrier bridge enqueue (future SimpleOS)
  SchedState.runBatch      ↔  run-until-idle loop (future SimpleOS carrier)
  ─────────────────────────────────────────────────────────────────────────────

  FINDING-T1: CLOSED — guard now in source and model
  ────────────────────────────────────────────────────
  green_task_complete now guards on state == GREEN_TASK_DONE at entry; a second
  call with any result is a no-op (first-write-wins).  GreenTask.complete in
  Basic.lean models this guard.  T5b below is upgraded from same-result
  idempotency to full double-complete safety: the second call with ANY result
  is identity.

  FINDING-T2: No run-until-idle loop in green_task/green_worker source
  ──────────────────────────────────────────────────────────────────────
  green_task.spl and green_worker.spl are pure placement-logic helpers.
  They contain no scheduling loop.  The run-until-idle semantics is
  modelled here as SchedState.runBatch (structural recursion on the queue).
  T6 proves termination and idle-when-empty.

  Theorems
  ════════
  T1  new_is_runnable          — freshly spawned task is in runnable state
  T2  park_preserves_cpu       — park does not change home_cpu or assigned_cpu
  T3  unpark_parked_enqueues   — unpark of a parked task sets should_enqueue=true
  T4  unpark_nonparked_noop    — unpark of non-parked task is identity (no-op)
  T5a complete_marks_done      — complete sets state to done
  T5b complete_double_safe     — complete twice with ANY result is identity (first-write-wins)
  T6  runBatch_empties_queue   — runBatch terminates and leaves queue empty
  T7  enqueue_then_runBatch    — an enqueued task is consumed by runBatch
  T8  cpuAllowed_zero_mask     — mask=0 allows every non-negative cpu index
  T9  steal_threshold_correct  — steal iff remote − local > threshold
  T10 resource_pool_safe       — acquire/release preserve capacity and never underflow
-/

import KernelScheduler.Basic

namespace KernelScheduler

-- ============================================================
-- § A  T1 — new_is_runnable
-- ============================================================

/-- T1: A freshly created task is always in the runnable state.
    Mirrors: green_task_new always sets state = GREEN_TASK_RUNNABLE. -/
theorem new_is_runnable (tid home_cpu affinity : Nat) :
    (GreenTask.new tid home_cpu affinity).state = .runnable := by
  simp [GreenTask.new]

/-- T1b: A freshly created task has home_cpu = assigned_cpu. -/
theorem new_home_eq_assigned (tid home_cpu affinity : Nat) :
    (GreenTask.new tid home_cpu affinity).home_cpu =
    (GreenTask.new tid home_cpu affinity).assigned_cpu := by
  simp [GreenTask.new]

/-- T1c: new returns the exact runnable task record. -/
theorem new_eq_runnable_record (tid home_cpu affinity : Nat) :
    GreenTask.new tid home_cpu affinity =
      { task_id := tid
      , home_cpu := home_cpu
      , assigned_cpu := home_cpu
      , affinity_mask := affinity
      , state := .runnable
      , park_reason := ""
      , result_val := 0 } := by
  simp [GreenTask.new]

-- ============================================================
-- § B  T2 — park_preserves_cpu
-- ============================================================

/-- T2: park does not change home_cpu.
    Mirrors: green_task_park copies home_cpu unchanged. -/
theorem park_preserves_home_cpu (t : GreenTask) (reason : String) :
    (t.park reason).home_cpu = t.home_cpu := by
  simp [GreenTask.park]

/-- T2b: park does not change assigned_cpu. -/
theorem park_preserves_assigned_cpu (t : GreenTask) (reason : String) :
    (t.park reason).assigned_cpu = t.assigned_cpu := by
  simp [GreenTask.park]

/-- T2c: park transitions state to parked. -/
theorem park_state (t : GreenTask) (reason : String) :
    (t.park reason).state = .parked := by
  simp [GreenTask.park]

/-- T2c2: park records the supplied park reason. -/
theorem park_records_reason (t : GreenTask) (reason : String) :
    (t.park reason).park_reason = reason := by
  simp [GreenTask.park]

/-- T2c3: park returns the exact parked task record. -/
theorem park_eq_parked_record (t : GreenTask) (reason : String) :
    t.park reason =
      { task_id := t.task_id
      , home_cpu := t.home_cpu
      , assigned_cpu := t.assigned_cpu
      , affinity_mask := t.affinity_mask
      , state := .parked
      , park_reason := reason
      , result_val := t.result_val } := by
  simp [GreenTask.park]

/-- T2d: park preserves task identity. -/
theorem park_preserves_task_id (t : GreenTask) (reason : String) :
    (t.park reason).task_id = t.task_id := by
  simp [GreenTask.park]

-- ============================================================
-- § C  T3 — unpark_parked_enqueues
-- ============================================================

/-- T3: unpark of a parked task always produces should_enqueue = true. -/
theorem unpark_parked_enqueues (t : GreenTask) (waker_cpu : Nat)
    (hparked : t.state = .parked) :
    (t.unpark waker_cpu).should_enqueue = true := by
  simp [GreenTask.unpark, hparked]

/-- T3b: unpark of a parked task sets state back to runnable. -/
theorem unpark_parked_runnable (t : GreenTask) (waker_cpu : Nat)
    (hparked : t.state = .parked) :
    (t.unpark waker_cpu).task.state = .runnable := by
  simp [GreenTask.unpark, hparked]

/-- T3c: unpark clears park_reason. -/
theorem unpark_clears_reason (t : GreenTask) (waker_cpu : Nat)
    (hparked : t.state = .parked) :
    (t.unpark waker_cpu).task.park_reason = "" := by
  simp [GreenTask.unpark, hparked]

/-- T3c2: unpark of a parked task assigns it to the waker CPU. -/
theorem unpark_parked_sets_assigned_cpu (t : GreenTask) (waker_cpu : Nat)
    (hparked : t.state = .parked) :
    (t.unpark waker_cpu).task.assigned_cpu = waker_cpu := by
  simp [GreenTask.unpark, hparked]

/-- T3c3: unpark of a parked task reports the waker CPU placement. -/
theorem unpark_parked_reports_waker_placement (t : GreenTask) (waker_cpu : Nat)
    (hparked : t.state = .parked) :
    (t.unpark waker_cpu).placement.cpu = waker_cpu ∧
    (t.unpark waker_cpu).placement.reason = "wake_affine_waker_cpu" := by
  simp [GreenTask.unpark, hparked]

/-- T3c4: unpark of a parked task returns the exact runnable task record. -/
theorem unpark_parked_task_eq_runnable_record (t : GreenTask) (waker_cpu : Nat)
    (hparked : t.state = .parked) :
    (t.unpark waker_cpu).task =
      { task_id := t.task_id
      , home_cpu := t.home_cpu
      , assigned_cpu := waker_cpu
      , affinity_mask := t.affinity_mask
      , state := .runnable
      , park_reason := ""
      , result_val := t.result_val } := by
  simp [GreenTask.unpark, hparked]

/-- T3c5: unpark of a parked task returns the exact enqueue wake decision. -/
theorem unpark_parked_eq_enqueue_decision (t : GreenTask) (waker_cpu : Nat)
    (hparked : t.state = .parked) :
    t.unpark waker_cpu =
      { task :=
          { task_id := t.task_id
          , home_cpu := t.home_cpu
          , assigned_cpu := waker_cpu
          , affinity_mask := t.affinity_mask
          , state := .runnable
          , park_reason := ""
          , result_val := t.result_val }
      , placement := { cpu := waker_cpu, reason := "wake_affine_waker_cpu" }
      , should_enqueue := true } := by
  simp [GreenTask.unpark, hparked]

/-- T3d: unpark of a parked task preserves task identity. -/
theorem unpark_parked_preserves_task_id (t : GreenTask) (waker_cpu : Nat)
    (hparked : t.state = .parked) :
    (t.unpark waker_cpu).task.task_id = t.task_id := by
  simp [GreenTask.unpark, hparked]

-- ============================================================
-- § D  T4 — unpark_nonparked_noop
-- ============================================================

/-- T4: unpark of a NON-parked task is a no-op (should_enqueue = false).
    Mirrors: green_task_unpark checks state != GREEN_TASK_PARKED and
    returns should_enqueue=false unchanged. -/
theorem unpark_nonparked_noop (t : GreenTask) (waker_cpu : Nat)
    (hnot_parked : t.state ≠ .parked) :
    (t.unpark waker_cpu).should_enqueue = false := by
  simp [GreenTask.unpark, if_neg hnot_parked]

/-- T4b: unpark of a non-parked task returns the task unchanged. -/
theorem unpark_nonparked_task_id (t : GreenTask) (waker_cpu : Nat)
    (hnot_parked : t.state ≠ .parked) :
    (t.unpark waker_cpu).task = t := by
  simp [GreenTask.unpark, if_neg hnot_parked]

/-- T4c: unpark of a non-parked task reports no placement move. -/
theorem unpark_nonparked_reports_no_move (t : GreenTask) (waker_cpu : Nat)
    (hnot_parked : t.state ≠ .parked) :
    (t.unpark waker_cpu).placement.cpu = t.assigned_cpu ∧
    (t.unpark waker_cpu).placement.reason = "not_parked" := by
  simp [GreenTask.unpark, if_neg hnot_parked]

/-- T4d: unpark of a non-parked task returns the exact no-op wake decision. -/
theorem unpark_nonparked_eq_noop_decision (t : GreenTask) (waker_cpu : Nat)
    (hnot_parked : t.state ≠ .parked) :
    t.unpark waker_cpu =
      { task := t
      , placement := { cpu := t.assigned_cpu, reason := "not_parked" }
      , should_enqueue := false } := by
  simp [GreenTask.unpark, if_neg hnot_parked]

/-- T4e: A completed task cannot be woken back onto a ready queue. -/
theorem unpark_done_no_enqueue (t : GreenTask) (waker_cpu : Nat)
    (hdone : t.state = .done) :
    (t.unpark waker_cpu).should_enqueue = false ∧ (t.unpark waker_cpu).task = t := by
  have hnot : t.state ≠ .parked := by
    intro hparked
    rw [hdone] at hparked
    cases hparked
  simp [GreenTask.unpark, if_neg hnot]

-- ============================================================
-- § E  T5 — complete
-- ============================================================

/-- T5a: complete always results in state = done.
    Mirrors: green_task_complete sets state = GREEN_TASK_DONE when not already done;
    when already done the guard returns t unchanged (state is already done). -/
theorem complete_marks_done (t : GreenTask) (r : Int) :
    (t.complete r).state = .done := by
  unfold GreenTask.complete
  by_cases h : t.state = .done
  · simp [h]
  · simp [h]

/-- T5b: double-complete safety (full first-write-wins).
    FINDING-T1 CLOSED: the guard is now in the source and in GreenTask.complete.
    A second call to complete with ANY result on an already-done task is
    identity — the record is unchanged and the first result is preserved. -/
theorem complete_double_safe (t : GreenTask) (r1 r2 : Int) :
    (t.complete r1).complete r2 = t.complete r1 := by
  unfold GreenTask.complete
  by_cases h : t.state = .done
  · simp [h]
  · simp [h]

/-- T5b1: a second completion cannot overwrite the first completion result. -/
theorem complete_double_preserves_first_result (t : GreenTask) (r1 r2 : Int) :
    ((t.complete r1).complete r2).result_val = (t.complete r1).result_val := by
  rw [complete_double_safe t r1 r2]

/-- T5b0: complete on an already-done task is a no-op. -/
theorem complete_done_noop (t : GreenTask) (r : Int)
    (h : t.state = .done) :
    t.complete r = t := by
  simp [GreenTask.complete, h]

/-- T5c: complete preserves CPU placement/accounting fields. -/
theorem complete_preserves_cpu_assignment (t : GreenTask) (r : Int) :
    (t.complete r).home_cpu = t.home_cpu ∧
    (t.complete r).assigned_cpu = t.assigned_cpu := by
  unfold GreenTask.complete
  by_cases h : t.state = .done <;> simp [h]

/-- T5d: completing a non-done task records the result value. -/
theorem complete_records_result_when_not_done (t : GreenTask) (r : Int)
    (h : t.state ≠ .done) :
    (t.complete r).result_val = r := by
  simp [GreenTask.complete, h]

/-- T5d2: completing a non-done task returns the exact done-state record. -/
theorem complete_non_done_eq_done_record (t : GreenTask) (r : Int)
    (h : t.state ≠ .done) :
    t.complete r =
      { task_id := t.task_id
      , home_cpu := t.home_cpu
      , assigned_cpu := t.assigned_cpu
      , affinity_mask := t.affinity_mask
      , state := .done
      , park_reason := t.park_reason
      , result_val := r } := by
  simp [GreenTask.complete, h]

/-- T5e: complete preserves task identity. -/
theorem complete_preserves_task_id (t : GreenTask) (r : Int) :
    (t.complete r).task_id = t.task_id := by
  unfold GreenTask.complete
  by_cases h : t.state = .done <;> simp [h]

-- ============================================================
-- § F  T6 — runBatch terminates and empties the queue
-- ============================================================

/-- T6: runBatch always produces an empty ready queue.
    Mirrors the run-until-idle contract: the scheduler exits only when
    the ready queue is empty. -/
theorem runBatch_empty (s : SchedState) :
    (SchedState.runBatch s).ready = [] := by
  induction s with
  | mk ready =>
    induction ready with
    | nil => simp [SchedState.runBatch]
    | cons _ rest ih =>
      simp [SchedState.runBatch]
      exact ih

-- ============================================================
-- § G  T7 — enqueue_then_runBatch
-- ============================================================

/-- T7: A task enqueued into an empty scheduler is consumed by runBatch.
    Mirrors: the carrier bridge enqueues a runnable task; run-until-idle
    drains it; no tasks are lost. -/
theorem enqueue_then_runBatch_empty (t : GreenTask) :
    let s0 : SchedState := { ready := [] }
    let s1 := s0.enqueue t
    (SchedState.runBatch s1).ready = [] := by
  simp [SchedState.enqueue, SchedState.runBatch]

/-- T7a1: enqueue appends exactly one ready task. -/
theorem enqueue_increases_ready_length (s : SchedState) (t : GreenTask) :
    (s.enqueue t).ready.length = s.ready.length + 1 := by
  simp [SchedState.enqueue]

/-- T7a2: enqueue preserves queue order and appends the task at the tail. -/
theorem enqueue_ready_eq_append (s : SchedState) (t : GreenTask) :
    (s.enqueue t).ready = s.ready ++ [t] := by
  simp [SchedState.enqueue]

/-- T7b: runBatch on an already-empty state is the identity. -/
theorem runBatch_empty_is_empty :
    (SchedState.runBatch { ready := [] }).ready = [] := by
  simp [SchedState.runBatch]

/-- T7c: popHead on a non-empty queue returns the head and the rest. -/
theorem popHead_nonempty_returns_head (t : GreenTask) (rest : List GreenTask) :
    SchedState.popHead { ready := t :: rest } = (some t, { ready := rest }) := by
  simp [SchedState.popHead]

/-- T7d: popHead on an empty queue reports no task and leaves the queue empty. -/
theorem popHead_empty_noop :
    SchedState.popHead { ready := [] } = (none, { ready := [] }) := by
  simp [SchedState.popHead]

/-- T7e: runOne on an empty queue is identity. -/
theorem runOne_empty_noop :
    SchedState.runOne { ready := [] } = { ready := [] } := by
  simp [SchedState.runOne, SchedState.popHead]

/-- T7f: runOne on a non-empty queue consumes exactly the head. -/
theorem runOne_nonempty_drops_head (t : GreenTask) (rest : List GreenTask) :
    SchedState.runOne { ready := t :: rest } = { ready := rest } := by
  simp [SchedState.runOne, SchedState.popHead]

/-- T7g: runOne on a non-empty queue strictly decreases ready length. -/
theorem runOne_nonempty_decreases_length (t : GreenTask) (rest : List GreenTask) :
    (SchedState.runOne { ready := t :: rest }).ready.length < (t :: rest).length := by
  simp [SchedState.runOne, SchedState.popHead]

/-- T7h: a task enqueued into an empty ready queue is consumed by the next
    scheduler tick. -/
theorem enqueue_empty_then_runOne_empty (t : GreenTask) :
    SchedState.runOne (({ ready := [] } : SchedState).enqueue t) = { ready := [] } := by
  simp [SchedState.enqueue, SchedState.runOne, SchedState.popHead]

/-- Run a bounded number of scheduler ticks.  This is the finite-step view used
    to state service latency without assuming a coinductive scheduler loop. -/
def runOneSteps : Nat → SchedState → SchedState
  | 0, s => s
  | n + 1, s => runOneSteps n (SchedState.runOne s)

/-- T7i: each scheduler tick consumes one queued task until the queue is empty,
    giving a finite service bound equal to the initial ready-queue length in the
    no-requeue model. -/
theorem runOne_service_bound_by_ready_length (ready : List GreenTask) :
    (runOneSteps ready.length { ready := ready }).ready = [] := by
  induction ready with
  | nil =>
      simp [runOneSteps]
  | cons t rest ih =>
      simp [runOneSteps, SchedState.runOne, SchedState.popHead, ih]

-- ============================================================
-- § H  T8 — cpuAllowed semantics
-- ============================================================

/-- T8a: mask = 0 allows any cpu (unrestricted affinity).
    Mirrors: green_worker_cpu_allowed returns true when affinity_mask == 0. -/
theorem cpuAllowed_zero_mask (cpu : Nat) :
    cpuAllowed 0 cpu = true := by
  simp [cpuAllowed]

/-- T8b: mask ≠ 0 denies a cpu when its bit is not set. -/
theorem cpuAllowed_bit_not_set (mask cpu : Nat)
    (hmask : mask ≠ 0)
    (hbit  : mask &&& (1 <<< cpu) = 0) :
    cpuAllowed mask cpu = false := by
  simp [cpuAllowed, hmask, hbit]

/-- T8c: mask ≠ 0 allows a cpu when its bit IS set. -/
theorem cpuAllowed_bit_set (mask cpu : Nat)
    (hmask : mask ≠ 0)
    (hbit  : mask &&& (1 <<< cpu) ≠ 0) :
    cpuAllowed mask cpu = true := by
  simp [cpuAllowed, hmask, hbit]

/-- T8d: cpuAllowed is exactly unrestricted mask or set CPU bit. -/
theorem cpuAllowed_true_iff (mask cpu : Nat) :
    cpuAllowed mask cpu = true ↔ mask = 0 ∨ mask &&& (1 <<< cpu) ≠ 0 := by
  unfold cpuAllowed
  by_cases hmask : mask = 0 <;> simp [hmask]

-- ============================================================
-- § I  T9 — shouldSteal threshold
-- ============================================================

/-- T9a: steal fires when remote load strictly exceeds local + threshold.
    Mirrors: green_worker_should_steal returns (remote - local) > threshold. -/
theorem steal_fires_above_threshold (local_load remote_load threshold : Nat)
    (h : remote_load > local_load + threshold) :
    shouldSteal local_load remote_load threshold = true := by
  simp [shouldSteal, h]

/-- T9a0: shouldSteal is exactly the remote-load threshold gate. -/
theorem shouldSteal_true_iff (local_load remote_load threshold : Nat) :
    shouldSteal local_load remote_load threshold = true ↔
    remote_load > local_load + threshold := by
  simp [shouldSteal]

/-- T9b: steal does NOT fire when remote load is at or below local + threshold. -/
theorem steal_does_not_fire_at_threshold (local_load remote_load threshold : Nat)
    (h : remote_load ≤ local_load + threshold) :
    shouldSteal local_load remote_load threshold = false := by
  simp [shouldSteal]
  omega

/-- T9b0: shouldSteal is false exactly at or below the threshold. -/
theorem shouldSteal_false_iff (local_load remote_load threshold : Nat) :
    shouldSteal local_load remote_load threshold = false ↔
    remote_load ≤ local_load + threshold := by
  simp [shouldSteal]

-- ============================================================
-- § J  T10 — bounded resource lifecycle safety
-- ============================================================

/-- T10a: acquire below capacity grants exactly one additional live resource. -/
theorem resource_acquire_below_capacity_grants (p : ResourcePool)
    (h : p.inUse < p.capacity) :
    (p.acquire).granted = true ∧ (p.acquire).pool.inUse = p.inUse + 1 := by
  simp [ResourcePool.acquire, h]

/-- T10a0a: successful acquire returns exactly the one-increment pool. -/
theorem resource_acquire_below_capacity_pool_eq (p : ResourcePool)
    (h : p.inUse < p.capacity) :
    (p.acquire).pool = { capacity := p.capacity, inUse := p.inUse + 1 } := by
  simp [ResourcePool.acquire, h]

/-- T10a0aa: successful acquire returns the exact granted acquire result. -/
theorem resource_acquire_below_capacity_eq_granted_result (p : ResourcePool)
    (h : p.inUse < p.capacity) :
    p.acquire =
      { pool := { capacity := p.capacity, inUse := p.inUse + 1 }
      , granted := true } := by
  simp [ResourcePool.acquire, h]

/-- T10a0b: successful acquire preserves resource capacity. -/
theorem resource_acquire_below_capacity_preserves_capacity (p : ResourcePool)
    (h : p.inUse < p.capacity) :
    (p.acquire).pool.capacity = p.capacity := by
  simp [ResourcePool.acquire, h]

/-- T10a0c: successful acquire produces a well-formed pool. -/
theorem resource_acquire_below_capacity_wf (p : ResourcePool)
    (h : p.inUse < p.capacity) :
    (p.acquire).pool.wf := by
  unfold ResourcePool.acquire ResourcePool.wf
  simp [h]
  omega

/-- T10a0: acquire grants iff capacity remains. -/
theorem resource_acquire_granted_iff_below_capacity (p : ResourcePool) :
    (p.acquire).granted = true ↔ p.inUse < p.capacity := by
  unfold ResourcePool.acquire
  by_cases h : p.inUse < p.capacity <;> simp [h]

/-- T10a1: successful acquire strictly increases live resources. -/
theorem resource_acquire_below_capacity_increases (p : ResourcePool)
    (h : p.inUse < p.capacity) :
    p.inUse < (p.acquire).pool.inUse := by
  have hgrant := resource_acquire_below_capacity_grants p h
  omega

/-- T10a2: acquire never decreases live resources. -/
theorem resource_acquire_never_decreases (p : ResourcePool) :
    p.inUse ≤ (p.acquire).pool.inUse := by
  unfold ResourcePool.acquire
  by_cases h : p.inUse < p.capacity <;> simp [h]

/-- T10b: acquire at capacity is a no-op and reports denial. -/
theorem resource_acquire_full_noop (p : ResourcePool)
    (h : p.capacity ≤ p.inUse) :
    (p.acquire).granted = false ∧ (p.acquire).pool = p := by
  have hn : ¬ p.inUse < p.capacity := by omega
  simp [ResourcePool.acquire, hn]

/-- T10b0a: denied acquire returns the exact no-op acquire result. -/
theorem resource_acquire_full_eq_denied_result (p : ResourcePool)
    (h : p.capacity ≤ p.inUse) :
    p.acquire = { pool := p, granted := false } := by
  have hn : ¬ p.inUse < p.capacity := by omega
  simp [ResourcePool.acquire, hn]

/-- T10b0: acquire denies iff no capacity remains. -/
theorem resource_acquire_denied_iff_at_capacity (p : ResourcePool) :
    (p.acquire).granted = false ↔ p.capacity ≤ p.inUse := by
  unfold ResourcePool.acquire
  by_cases h : p.inUse < p.capacity
  · simp [h]
  · simp [h]
    omega

/-- T10b1: failed acquire preserves the live resource count. -/
theorem resource_acquire_denied_preserves_in_use (p : ResourcePool)
    (h : p.capacity ≤ p.inUse) :
    (p.acquire).pool.inUse = p.inUse := by
  have hnoop := resource_acquire_full_noop p h
  exact congrArg ResourcePool.inUse hnoop.2

/-- T10b1b: failed acquire preserves the resource capacity. -/
theorem resource_acquire_denied_preserves_capacity (p : ResourcePool)
    (h : p.capacity ≤ p.inUse) :
    (p.acquire).pool.capacity = p.capacity := by
  have hnoop := resource_acquire_full_noop p h
  exact congrArg ResourcePool.capacity hnoop.2

/-- T10b2: a zero-capacity resource pool never grants acquisition. -/
theorem resource_zero_capacity_acquire_denied (p : ResourcePool)
    (hcap : p.capacity = 0) :
    (p.acquire).granted = false ∧ (p.acquire).pool = p := by
  apply resource_acquire_full_noop
  omega

/-- T10b3: a well-formed zero-capacity pool has no live resources. -/
theorem resource_zero_capacity_wf_empty (p : ResourcePool)
    (hcap : p.capacity = 0)
    (hwf : p.wf) :
    p.inUse = 0 := by
  unfold ResourcePool.wf at hwf
  omega

/-- T10c: release of an empty pool is a no-op. -/
theorem resource_release_empty_noop (p : ResourcePool)
    (h : p.inUse = 0) :
    p.release = p := by
  simp [ResourcePool.release, h]

/-- T10c0: release is a no-op iff no resources are live. -/
theorem resource_release_noop_iff_empty (p : ResourcePool) :
    p.release = p ↔ p.inUse = 0 := by
  constructor
  · intro hrel
    by_cases h : p.inUse = 0
    · exact h
    · have hin := congrArg ResourcePool.inUse hrel
      simp [ResourcePool.release, h] at hin
      omega
  · intro h
    simp [ResourcePool.release, h]

/-- T10c0b: release of a non-empty pool is not a no-op. -/
theorem resource_release_nonempty_not_noop (p : ResourcePool)
    (h : p.inUse ≠ 0) :
    p.release ≠ p := by
  intro hrel
  have hempty := (resource_release_noop_iff_empty p).mp hrel
  exact h hempty

/-- T10c1: release of a non-empty pool preserves capacity. -/
theorem resource_release_nonempty_preserves_capacity (p : ResourcePool)
    (h : p.inUse ≠ 0) :
    p.release.capacity = p.capacity := by
  simp [ResourcePool.release, h]

/-- T10c1b: release of a non-empty pool returns exactly the one-decrement pool. -/
theorem resource_release_nonempty_pool_eq (p : ResourcePool)
    (h : p.inUse ≠ 0) :
    p.release = { capacity := p.capacity, inUse := p.inUse - 1 } := by
  simp [ResourcePool.release, h]

/-- T10c2: release of a non-empty pool decrements the live resource count. -/
theorem resource_release_nonempty_decrements (p : ResourcePool)
    (h : p.inUse ≠ 0) :
    p.release.inUse = p.inUse - 1 := by
  simp [ResourcePool.release, h]

/-- T10c3: release of a non-empty pool strictly reduces live resources. -/
theorem resource_release_nonempty_decreases (p : ResourcePool)
    (h : p.inUse ≠ 0) :
    p.release.inUse < p.inUse := by
  have hdec := resource_release_nonempty_decrements p h
  omega

/-- T10d: release never increases live resources, so it cannot underflow. -/
theorem resource_release_never_underflows (p : ResourcePool) :
    p.release.inUse ≤ p.inUse := by
  unfold ResourcePool.release
  by_cases h : p.inUse = 0
  · simp [h]
  · simp [h]

/-- T10e: acquire preserves the bounded-resource invariant. -/
theorem resource_acquire_preserves_wf (p : ResourcePool)
    (hwf : p.wf) :
    (p.acquire).pool.wf := by
  unfold ResourcePool.acquire ResourcePool.wf at *
  by_cases h : p.inUse < p.capacity
  · simp [h]
    omega
  · simp [h]
    exact hwf

/-- T10f: release preserves the bounded-resource invariant. -/
theorem resource_release_preserves_wf (p : ResourcePool)
    (hwf : p.wf) :
    p.release.wf := by
  unfold ResourcePool.release ResourcePool.wf at *
  by_cases h : p.inUse = 0
  · simp [h]
  · simp [h]
    omega

/-- T10f2: release preserves capacity and keeps live resources within the
    original capacity bound. -/
theorem resource_release_preserves_capacity_bound (p : ResourcePool)
    (hwf : p.wf) :
    p.release.capacity = p.capacity ∧ p.release.inUse ≤ p.capacity := by
  have hcap : p.release.capacity = p.capacity := by
    unfold ResourcePool.release
    by_cases h : p.inUse = 0 <;> simp [h]
  have hrel := resource_release_preserves_wf p hwf
  unfold ResourcePool.wf at hrel
  exact ⟨hcap, by simpa [hcap] using hrel⟩

/-- T10f3: acquire preserves capacity and keeps live resources within the
    original capacity bound for well-formed pools. -/
theorem resource_acquire_preserves_capacity_bound (p : ResourcePool)
    (hwf : p.wf) :
    (p.acquire).pool.capacity = p.capacity ∧ (p.acquire).pool.inUse ≤ p.capacity := by
  unfold ResourcePool.acquire ResourcePool.wf at *
  by_cases h : p.inUse < p.capacity
  · simp [h]
    omega
  · simp [h]
    exact hwf

/-- T10f4: releasing a live resource from a well-formed pool reopens exactly
    one acquire slot; the next acquire grants and restores the original pool. -/
theorem resource_release_nonempty_then_acquire_eq_granted_original (p : ResourcePool)
    (hwf : p.wf)
    (h : p.inUse ≠ 0) :
    p.release.acquire = { pool := p, granted := true } := by
  unfold ResourcePool.release ResourcePool.acquire ResourcePool.wf at *
  have hpos : 0 < p.inUse := Nat.pos_of_ne_zero h
  have hslot : p.inUse - 1 < p.capacity := by omega
  have hrestore : p.inUse - 1 + 1 = p.inUse := by omega
  simp [h, hslot, hrestore]

/-- T10g: successful acquire followed by release returns the pool to its
    original state.  This is the basic no-leak lifecycle roundtrip. -/
theorem resource_acquire_release_roundtrip (p : ResourcePool)
    (h : p.inUse < p.capacity) :
    (p.acquire).pool.release = p := by
  unfold ResourcePool.acquire ResourcePool.release
  simp [h]

/-- T10h: denied acquire is observationally neutral for cleanup: releasing
    after a full acquire attempt is exactly the same as releasing the original
    pool. -/
theorem resource_denied_acquire_then_release_eq_release (p : ResourcePool)
    (h : p.capacity ≤ p.inUse) :
    (p.acquire).pool.release = p.release := by
  have hn : ¬ p.inUse < p.capacity := by omega
  simp [ResourcePool.acquire, hn]

/-- T10i: after a successful acquire/release roundtrip, an extra release is
    exactly the same as releasing the original pool. -/
theorem resource_acquire_release_release_eq_release (p : ResourcePool)
    (h : p.inUse < p.capacity) :
    (p.acquire).pool.release.release = p.release := by
  rw [resource_acquire_release_roundtrip p h]

end KernelScheduler
