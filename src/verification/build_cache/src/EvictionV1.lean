/-
  EvictionV1 — T-EV1: eviction never changes semantics.

  Models the APPLICATION of cache_eviction_plan_v1
  (src/compiler/80.driver/cache/gc/cache_eviction_plan_v1.spl): a plan names
  entries to evict (disk) or unload (memory); applying it removes entries and
  never rewrites one. Plan: cache_invalidation_formal_verification_2026-10-24.md §4.1 T-EV1.
  SSpec twin (bounded, over the real planner):
  test/00_formal_verification/compiler/cache_eviction_neutral_bounded_spec.spl

  Proved: a lookup after eviction returns the old value or a miss
  (read_after_evict_same_or_miss), a miss never fabricates content, pinned
  entries survive any admissible plan (pinned_survive), and a root-closed plan
  leaves no dangling reference (root_closed_no_dangling).
  plan_can_split_referrer (proved): a per-entry plan that ignores reference
  edges can keep a referrer and evict its referent. The landed planner was
  made reference-aware by 8f2c6dd7f1e ("never evict an entry a kept entry
  references"), i.e. it now aims at RootClosed, the premise of
  root_closed_no_dangling; the bounded twin checks pins and byte accounting
  but not yet reference closure.
  No sorry, no axioms.
-/
namespace EvictionV1

abbrev Key := String

structure Entry where
  key    : Key
  value  : String
  pinned : Bool
  refs   : List Key     -- entries this one needs (manifest -> object, ...)
  deriving DecidableEq, Repr

abbrev Store := List Entry

def lookup (s : Store) (k : Key) : Option String :=
  (s.find? (fun e => e.key == k)).map Entry.value

/-- Applying a plan: drop every entry the plan names. -/
def evict (s : Store) (plan : Key → Bool) : Store := s.filter (fun e => !plan e.key)

/-- A plan is admissible when it never names a pinned entry (live_views > 0). -/
def Admissible (s : Store) (plan : Key → Bool) : Prop := ∀ e ∈ s, e.pinned = true → plan e.key = false

/-- T-EV1 (neutrality): after eviction a key reads its old value or misses. -/
theorem read_after_evict_same_or_miss (s : Store) (plan : Key → Bool) (k : Key)
    (huniq : (s.filter (fun e => e.key == k)).length ≤ 1) :
    lookup (evict s plan) k = lookup s k ∨ lookup (evict s plan) k = none := by
  unfold lookup evict
  by_cases hk : plan k = true
  · right
    have : (s.filter (fun e => !plan e.key)).find? (fun e => e.key == k) = none := by
      rw [List.find?_eq_none]
      intro e he hek
      simp [List.mem_filter] at he
      simp at hek
      rw [hek] at he
      simp [hk] at he
    simp [this]
  · left
    have hk' : plan k = false := by simpa using hk
    congr 1
    induction s with
    | nil => rfl
    | cons e es ih =>
      by_cases he : e.key = k
      · subst he
        simp [List.filter, hk', List.find?]
      · have hne : (e.key == k) = false := by simpa using he
        have hu : (es.filter (fun e => e.key == k)).length ≤ 1 := by
          simp [List.filter, hne] at huniq; simpa [List.filter] using huniq
        cases hp : plan e.key <;> simp [List.filter, hp, List.find?, hne, ih hu]

/-- A miss after eviction never fabricates content: any value read after
    eviction was in the store before. -/
theorem evict_no_fabrication (s : Store) (plan : Key → Bool) (e : Entry)
    (h : e ∈ evict s plan) : e ∈ s := by
  unfold evict at h; exact (List.mem_filter.mp h).1

/-- Pinned entries survive any admissible plan. -/
theorem pinned_survive (s : Store) (plan : Key → Bool) (hadm : Admissible s plan)
    (e : Entry) (he : e ∈ s) (hp : e.pinned = true) : e ∈ evict s plan := by
  unfold evict
  exact List.mem_filter.mpr ⟨he, by simp [hadm e he hp]⟩

/-- Root closure: a plan that never evicts a referent of a kept entry. -/
def RootClosed (s : Store) (plan : Key → Bool) : Prop :=
  ∀ e ∈ s, plan e.key = false → ∀ r ∈ e.refs, plan r = false

def NoDangling (s : Store) : Prop := ∀ e ∈ s, ∀ r ∈ e.refs, ∃ e' ∈ s, e'.key = r

theorem root_closed_no_dangling (s : Store) (plan : Key → Bool)
    (hd : NoDangling s) (hc : RootClosed s plan) : NoDangling (evict s plan) := by
  intro e he r hr
  have he' := List.mem_filter.mp he
  have hkeep : plan e.key = false := by simpa using he'.2
  obtain ⟨e', he's, hk⟩ := hd e he'.1 r hr
  refine ⟨e', List.mem_filter.mpr ⟨he's, ?_⟩, hk⟩
  have := hc e he'.1 hkeep r hr
  rw [hk]; simp [this]

/-- The gap: a per-entry plan (no root closure) can keep a referrer and evict
    its referent. -/
theorem plan_can_split_referrer :
    ∃ (s : Store) (plan : Key → Bool), NoDangling s ∧ Admissible s plan ∧
      ¬ NoDangling (evict s plan) := by
  refine ⟨[⟨"tldr", "t", false, ["obj"]⟩, ⟨"obj", "o", false, []⟩],
    fun k => k == "obj", ?_, ?_, ?_⟩
  · intro e he r hr
    simp at he
    rcases he with rfl | rfl
    · simp at hr; subst hr; exact ⟨⟨"obj", "o", false, []⟩, by simp, rfl⟩
    · simp at hr
  · intro e he hp
    simp at he
    rcases he with rfl | rfl <;> simp at hp
  · intro h
    obtain ⟨e', he', hk⟩ := h ⟨"tldr", "t", false, ["obj"]⟩ (by simp [evict]) "obj" (by simp)
    simp [evict] at he'
    rw [he'] at hk
    simp at hk

end EvictionV1
