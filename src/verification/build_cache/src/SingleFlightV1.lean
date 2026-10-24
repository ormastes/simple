/-
  SingleFlightV1 — T-SF1 for the LANDED single-flight table
  src/compiler/80.driver/cache/daemon/cache_single_flight_v1.spl
  (#4372 leader/waiter table, #4396 waiter wakeup + redrive).

  Replaces, for the live code, BuildCache.lean's lease/fence/owner-death model
  (claim_preserves_singleflight, stale_fence_cannot_publish), which describes
  a protocol nothing runs. Plan:
  doc/05_design/compiler/incremental_build/cache_invalidation_formal_verification_2026-10-24.md §4.1 T-SF1.

  The model is one key's slot; the Simple table keys slots by
  cache_single_flight_key_v1 and every operation touches only its own key.
  Correspondence (manual, pinned by source_bindings.txt):
    join      ↔ join_at (now = none ↔ join(), started_ms = -1)
    complete  ↔ complete (woken := waiters, flight/leader removed)
    redrive   ↔ redrive (`now - started < timeout` ⇔ `now < started + timeout`)
  No sorry, no axioms.
-/
namespace SingleFlightV1

abbrev Req := String

structure Flight where
  leader  : Req
  waiters : List Req
  started : Option Nat      -- none: joined through join(), no redrive clock
  deriving DecidableEq, Repr

structure Slot where
  inflight : Option Flight
  woken    : List Req        -- answered once the flight completes (take_woken)
  result   : Option (Option String)
  deriving DecidableEq, Repr

def join (s : Slot) (r : Req) (now : Option Nat) : Slot × Bool :=
  match s.inflight with
  | some f => ({ s with inflight := some { f with waiters := f.waiters ++ [r] } }, false)
  | none   => ({ s with inflight := some ⟨r, [], now⟩ }, true)

def complete (s : Slot) (r : Req) (blob : Option String) : Option Slot :=
  match s.inflight with
  | some f => if f.leader = r then some ⟨none, s.woken ++ f.waiters, some blob⟩ else none
  | none   => none

def redrive (s : Slot) (now timeout : Nat) : Slot :=
  match s.inflight with
  | some ⟨_, ws, some st⟩ =>
      if now < st + timeout then s else
      match ws with
      | []        => { s with inflight := none }
      | w :: rest => { s with inflight := some ⟨w, rest, some now⟩ }
  | _ => s

/-- Requests the slot still owes an answer to (leader + waiters) or has answered. -/
def participants (s : Slot) : List Req :=
  (match s.inflight with
   | some f => f.leader :: f.waiters
   | none   => []) ++ s.woken

-- ---------------------------------------------------------------------------
-- At most one leader; joins never displace it
-- ---------------------------------------------------------------------------

theorem join_leads_iff_idle (s : Slot) (r : Req) (now : Option Nat) :
    (join s r now).2 = true ↔ s.inflight = none := by
  unfold join; cases h : s.inflight <;> simp

theorem join_keeps_leader (s : Slot) (f : Flight) (r : Req) (now : Option Nat)
    (h : s.inflight = some f) :
    ((join s r now).1.inflight.map Flight.leader) = some f.leader := by
  unfold join; simp [h]

theorem join_records_request (s : Slot) (r : Req) (now : Option Nat) :
    r ∈ participants (join s r now).1 := by
  unfold join participants; cases h : s.inflight <;> simp

theorem join_loses_no_one (s : Slot) (r : Req) (now : Option Nat) (x : Req)
    (hx : x ∈ participants s) : x ∈ participants (join s r now).1 := by
  unfold join participants at *
  cases h : s.inflight <;> simp_all
  · rcases hx with hx | hx | hx <;> simp [hx]

-- ---------------------------------------------------------------------------
-- Only the current leader publishes; every waiter is woken exactly once
-- ---------------------------------------------------------------------------

theorem only_leader_completes (s s' : Slot) (r : Req) (b : Option String)
    (h : complete s r b = some s') : ∃ f, s.inflight = some f ∧ f.leader = r := by
  unfold complete at h
  cases hs : s.inflight with
  | none => simp [hs] at h
  | some f =>
    simp [hs] at h
    exact ⟨f, rfl, h.1⟩

theorem complete_wakes_waiters (s s' : Slot) (f : Flight) (r : Req) (b : Option String)
    (hs : s.inflight = some f) (h : complete s r b = some s') :
    s'.woken = s.woken ++ f.waiters ∧ s'.inflight = none ∧ s'.result = some b := by
  unfold complete at h
  simp [hs] at h
  obtain ⟨_, rfl⟩ := h
  simp

/-- A completed slot never completes again (no double publication). -/
theorem complete_once (s s' : Slot) (r r' : Req) (b b' : Option String)
    (h : complete s r b = some s') : complete s' r' b' = none := by
  unfold complete at h
  cases hs : s.inflight with
  | none => simp [hs] at h
  | some f =>
    simp [hs] at h
    obtain ⟨_, rfl⟩ := h
    simp [complete]

-- ---------------------------------------------------------------------------
-- Re-drive of abandoned (clocked) leaders
-- ---------------------------------------------------------------------------

theorem redrive_promotes_oldest_waiter (s : Slot) (l w : Req) (rest : List Req)
    (st now t : Nat) (hs : s.inflight = some ⟨l, w :: rest, some st⟩)
    (hexp : st + t ≤ now) :
    (redrive s now t).inflight = some ⟨w, rest, some now⟩ := by
  unfold redrive; simp [hs, Nat.not_lt.mpr hexp]

theorem redrive_drops_waiterless (s : Slot) (l : Req) (st now t : Nat)
    (hs : s.inflight = some ⟨l, [], some st⟩) (hexp : st + t ≤ now) :
    (redrive s now t).inflight = none := by
  unfold redrive; simp [hs, Nat.not_lt.mpr hexp]

theorem redrive_respects_timeout (s : Slot) (f : Flight) (st now t : Nat)
    (hs : s.inflight = some f) (hst : f.started = some st) (hlive : now < st + t) :
    redrive s now t = s := by
  obtain ⟨l, ws, started⟩ := f
  simp at hst; subst hst
  unfold redrive; simp [hs, hlive]

/-- Re-drive never loses a waiter: every waiter is still owed an answer. -/
theorem redrive_keeps_waiters (s : Slot) (f : Flight) (now t : Nat) (x : Req)
    (hs : s.inflight = some f) (hx : x ∈ f.waiters) : x ∈ participants (redrive s now t) := by
  obtain ⟨l, ws, started⟩ := f
  unfold redrive participants
  cases started with
  | none => simp [hs, hx]
  | some st =>
    by_cases hlive : now < st + t
    · simp [hs, hlive, hx]
    · cases ws with
      | nil => simp at hx
      | cons w rest =>
        simp [hs, hlive]
        simp at hx
        rcases hx with hx | hx <;> simp [hx]

/-- The abandoned leader can no longer publish after it was re-driven. -/
theorem stale_leader_cannot_complete (s : Slot) (l w : Req) (rest : List Req)
    (st now t : Nat) (b : Option String) (hs : s.inflight = some ⟨l, w :: rest, some st⟩)
    (hexp : st + t ≤ now) (hne : l ≠ w) :
    complete (redrive s now t) l b = none := by
  unfold complete
  rw [redrive_promotes_oldest_waiter s l w rest st now t hs hexp]
  simp [Ne.symm hne]

-- ---------------------------------------------------------------------------
-- The gap the proof exposes: UNCLOCKED flights (join(), started = -1) are
-- never re-driven, so a waiter on an abandoned unclocked leader waits forever.
-- In-process callers use join(): generic_instance_cache_v1, generic_tldr_view_
-- table_v1, macro_expansion_cache_v1. Only the daemon path (join_at) is clocked.
-- ---------------------------------------------------------------------------

theorem unclocked_flight_never_redriven (s : Slot) (l : Req) (ws : List Req) (now t : Nat)
    (hs : s.inflight = some ⟨l, ws, none⟩) : redrive s now t = s := by
  unfold redrive; simp [hs]

theorem unclocked_waiter_can_starve :
    ∃ s : Slot, ∃ w : Req, w ∈ participants s ∧ w ∉ s.woken ∧
      ∀ now t, redrive s now t = s :=
  ⟨⟨some ⟨"leader", ["waiter"], none⟩, [], none⟩, "waiter",
    by simp [participants], by simp,
    fun now t => unclocked_flight_never_redriven _ "leader" ["waiter"] now t rfl⟩

end SingleFlightV1
