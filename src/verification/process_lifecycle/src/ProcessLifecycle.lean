/-
  ProcessLifecycle -- Safety of Simple's process spawn/exit/wait/reap discipline.

  Grounds the model in the actual runtime:
    * spawn/run:   `rt_process_run` / `rt_process_spawn_async`
                   (src/lib/nogc_sync_mut/io_runtime.spl:18,36;
                    src/lib/nogc_sync_mut/platform.spl:12).
    * exit/reap:   the fork runtime reaps a child with `waitpid` and comments the
                   reap explicitly (src/runtime/runtime_fork.c:296 "Reap zombie",
                   :302 `waitpid(child_pid,&status,0)`), and rejects pid -1 so a
                   stray wait cannot reap every child (:143).

  We model a process as a state machine

        Created --run--> Running --exit--> Exited --reap--> Reaped

  and prove the four safety properties the discipline must give:

    * wait-before-exit blocks correctly: `doWait` returns a status ONLY for an
      Exited child (a wait on a live child blocks / yields nothing).
    * no double-reap: reaping an already-Reaped process is impossible; a reap
      strictly advances the lifecycle so a status is consumed exactly once.
    * no zombie persistence (invariant form, not liveness): any Exited process
      whose parent is waiting becomes Reaped in one collection step.
    * orphan handling: when a parent exits, its children are reparented to init
      (which always waits), so no Exited child is leaked unreaped.

  All theorems are proved without `sorry` (std only, no Mathlib).
-/
namespace ProcessLifecycle

/-- Lifecycle states, in strictly increasing lifetime order. `Exited` is the
    classic Unix zombie: the process has terminated and its exit status is
    pending a `waitpid`. `Reaped` is the terminal state after the parent
    consumed the status. -/
inductive ProcState
  | Created   -- fork issued; child not yet scheduled
  | Running   -- executing
  | Exited    -- terminated; status pending reap (zombie)
  | Reaped    -- status consumed by waitpid; slot reclaimed
  deriving DecidableEq, Repr

open ProcState

/-- A process-table entry. `parent` is the reaping pid (init's pid is `INIT`);
    `waiting` records that the parent is currently blocked in `wait()` on it.
    `resources` abstracts the per-task resource table entries owned by the
    process. -/
structure Proc where
  state   : ProcState
  parent  : Nat
  waiting : Bool
  resources : Nat
  deriving DecidableEq, Repr

/-- Conventional init pid that adopts orphans and always reaps. -/
def INIT : Nat := 1

/-- `spawn parent` mirrors `rt_process_spawn_async`: a fresh Created child that
    nobody is yet waiting on. -/
def spawn (parent : Nat) : Proc := { state := Created, parent := parent, waiting := false, resources := 0 }

/-! ### Guarded transitions (each returns `none` when not applicable). -/

/-- Schedule a Created process. -/
def doRun (p : Proc) : Option Proc :=
  match p.state with
  | Created => some { p with state := Running }
  | _       => none

/-- A Running process exits, becoming a zombie awaiting reap. -/
def doExit (p : Proc) : Option Proc :=
  match p.state with
  | Running => some { p with state := Exited, resources := 0 }
  | _       => none

/-- Reap an Exited process: this is the ONLY transition that consumes a status. -/
def doReap (p : Proc) : Option Proc :=
  match p.state with
  | Exited => some { p with state := Reaped }
  | _      => none

/-- `wait()` observes a child's terminal status: it yields `Exited` ONLY when the
    child has actually exited; on a live (Created/Running) child it blocks,
    modelled as `none`. Mirrors `waitpid(child,&status,0)` blocking semantics. -/
def doWait (p : Proc) : Option ProcState :=
  match p.state with
  | Exited => some Exited
  | _      => none

/-! ### Lifecycle ordering: transitions only ever advance (no resurrection). -/

def rank : ProcState → Nat
  | Created => 0
  | Running => 1
  | Exited  => 2
  | Reaped  => 3

theorem spawn_created (par : Nat) : (spawn par).state = Created := rfl

theorem run_from_created {p p' : Proc} (h : doRun p = some p') :
    p.state = Created ∧ p'.state = Running := by
  unfold doRun at h
  cases hs : p.state <;> rw [hs] at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
  subst h
  simp_all

theorem exit_from_running {p p' : Proc} (h : doExit p = some p') :
    p.state = Running ∧ p'.state = Exited := by
  unfold doExit at h
  cases hs : p.state <;> rw [hs] at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
  subst h
  simp_all

/-- Exit cleanup drains all per-task resources before the zombie can be reaped. -/
theorem exit_clears_resources {p p' : Proc} (h : doExit p = some p') :
    p'.resources = 0 := by
  unfold doExit at h
  cases hs : p.state <;> rw [hs] at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
  subst h
  rfl

/-- A reap is only ever applied to an Exited process. -/
theorem reap_requires_exited {p p' : Proc} (h : doReap p = some p') :
    p.state = Exited := by
  unfold doReap at h
  cases hs : p.state <;> rw [hs] at h <;> simp_all

/-- A reap yields the terminal Reaped state. -/
theorem reap_yields_reaped {p p' : Proc} (h : doReap p = some p') :
    p'.state = Reaped := by
  unfold doReap at h
  cases hs : p.state <;> rw [hs] at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
  subst h
  rfl

/-- Every transition strictly advances the lifecycle rank: no process is ever
    resurrected, so each state (and its pending status) is passed through once. -/
theorem exit_advances {p p' : Proc} (h : doExit p = some p') :
    rank p.state < rank p'.state := by
  obtain ⟨hs, hs'⟩ := exit_from_running h
  rw [hs, hs']; decide

theorem reap_advances {p p' : Proc} (h : doReap p = some p') :
    rank p.state < rank p'.state := by
  rw [reap_requires_exited h, reap_yields_reaped h]; decide

/-! ### wait-before-exit blocks correctly. -/

/-- `wait()` returns a status ONLY for an Exited child, and that status is
    exactly `Exited`. Hence a wait issued before the child exits cannot observe a
    bogus terminal status — it blocks. -/
theorem wait_returns_only_exited {p : Proc} {s : ProcState} (h : doWait p = some s) :
    p.state = Exited ∧ s = Exited := by
  unfold doWait at h
  cases hs : p.state <;> rw [hs] at h <;> simp_all

/-- Concretely, a wait on a Running child blocks. -/
theorem wait_blocks_on_running (p : Proc) (h : p.state = Running) :
    doWait p = none := by unfold doWait; rw [h]

/-- And a wait on a not-yet-scheduled child blocks too. -/
theorem wait_blocks_on_created (p : Proc) (h : p.state = Created) :
    doWait p = none := by unfold doWait; rw [h]

/-! ### No double-reap. -/

/-- Once reaped, a process can never be reaped again: the status is consumed
    exactly once. This is the `waitpid`-idempotence guarantee. -/
theorem no_double_reap {p p' : Proc} (h : doReap p = some p') :
    doReap p' = none := by
  unfold doReap
  rw [reap_yields_reaped h]

/-- A Reaped process admits no further transition of any kind (fully terminal). -/
theorem reaped_terminal (p : Proc) (h : p.state = Reaped) :
    doRun p = none ∧ doExit p = none ∧ doReap p = none := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [doRun, doExit, doReap, h]

/-! ### No zombie persistence (invariant / one-step simulation). -/

/-- A collection step: an Exited process whose parent is waiting is reaped;
    everything else is untouched. Models the parent's pending `waitpid` firing. -/
def collect (p : Proc) : Proc :=
  if p.state = Exited ∧ p.waiting = true then { p with state := Reaped } else p

/-- No zombie persists: any Exited process with a waiting parent is Reaped after
    a single collection step. Phrased as an invariant, not a liveness claim. -/
theorem no_zombie_persist (p : Proc) (he : p.state = Exited) (hw : p.waiting = true) :
    (collect p).state = Reaped := by
  unfold collect; simp [he, hw]

/-- Collection never regresses a process (rank is monotone), so it cannot create
    a zombie or resurrect a Reaped one. -/
theorem collect_monotone (p : Proc) : rank p.state ≤ rank (collect p).state := by
  unfold collect
  split
  · rename_i h; rw [h.1]; show rank Exited ≤ rank Reaped; decide
  · exact Nat.le_refl _

/-- Table-level: applying `collect` pointwise reaps every waiting-parent zombie. -/
theorem no_zombie_persist_table (tbl : Nat → Proc) (pid : Nat)
    (he : (tbl pid).state = Exited) (hw : (tbl pid).waiting = true) :
    (collect (tbl pid)).state = Reaped :=
  no_zombie_persist (tbl pid) he hw

/-! ### Orphan handling: reparent to init, no leaked Exited. -/

/-- When a parent exits, each surviving child is adopted by init, which always
    waits — so an already-Exited orphan is immediately reaped. -/
def adopt (p : Proc) : Proc :=
  collect { p with parent := INIT, waiting := true }

/-- Adoption reparents every child to init regardless of its state. -/
theorem adopt_reparents (p : Proc) : (adopt p).parent = INIT := by
  unfold adopt collect
  split <;> rfl

/-- No leaked zombie: an Exited orphan is Reaped once init adopts it. -/
theorem orphan_exited_reaped (p : Proc) (he : p.state = Exited) :
    (adopt p).state = Reaped := by
  unfold adopt
  apply no_zombie_persist <;> simp [he]

/-- A live orphan is never spuriously reaped: adoption leaves a Running child
    Running (only its parent changes), so nothing is lost. -/
theorem live_orphan_not_reaped (p : Proc) (hr : p.state = Running) :
    (adopt p).state = Running := by
  unfold adopt collect
  simp [hr]

end ProcessLifecycle
