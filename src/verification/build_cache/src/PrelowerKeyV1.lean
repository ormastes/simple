/-
  PrelowerKeyV1 — soundness of the native PRE-LOWERING object key
  (src/compiler/80.driver/cache/native_prelower_object_key.spl,
   driver side src/compiler/80.driver/driver_native_prelower_cache.spl).

  The key of module `m` carries m's own source digest, the build's module
  set, and for EVERY other module n a contribution: n's interface when n is
  body-opaque (no generic, trait/mixin, inline, macro, comptime), else n's
  full source. Plan: cache_invalidation_formal_verification_2026-10-24.md
  (known gaps cross_module_impl_set, inline_const_body, resolution_new_probe).

  Model: a source is (interface, bodies) — `split_inj` states the extractor
  is a deny-list that drops ONLY recognised fn bodies, so the pair determines
  the source. The producer and mono instances are folded into `extra`.
  Assumption (hypothesis `Reads`): m's object depends only on m's source,
  the module set, every other module's interface, the bodies of every
  NON-opaque module (bodies are copied only by generics/inline/trait default
  methods/macros/comptime), and `extra`. Advice is woven as a CALL
  (35.semantics/aspect_weave.spl, 50.mir/mir_aop_injection.spl), never by
  copying a body, so advice bodies need no special case.

  Proved: prelower_key_sound (equal key ⇒ equal object) and the three gap
  instances: an impl/extend header is an interface line
  (impl_header_change_changes_key), a copyable body of a non-opaque module
  is in the key (copyable_body_change_changes_key), and a new module in the
  build changes every key (new_module_changes_key).
  Bounded SSpec twin over the real extractor and opacity rule:
  test/00_formal_verification/compiler/native_prelower_key_bounded_spec.spl
  No sorry, no axioms.
-/
namespace PrelowerKeyV1

abbrev Name := String

structure Src where
  iface  : String       -- every non-blank line outside recognised fn bodies
  bodies : String       -- the fn bodies the extractor drops
  bodyOpaque : Bool         -- native_prelower_source_body_opaque_v1
  deriving DecidableEq, Repr

/-- The extractor drops only bodies: interface + bodies determine the source. -/
theorem split_inj (a b : Src) (hi : a.iface = b.iface) (hb : a.bodies = b.bodies)
    (ho : a.bodyOpaque = b.bodyOpaque) : a = b := by
  cases a; cases b; simp_all

/-- native_prelower_dependency_digest_v1: interface when opaque, else full source. -/
def contrib (s : Src) : String × Option String :=
  if s.bodyOpaque then (s.iface, none) else (s.iface, some s.bodies)

structure Build where
  names : List Name
  src   : Name → Src
  extra : String        -- producer identity + mono instances + lane

def key (b : Build) (m : Name) : Src × List Name × List (String × Option String) × String :=
  (b.src m, b.names, (b.names.filter (· ≠ m)).map (fun n => contrib (b.src n)), b.extra)

/-- What module m's object may read (the stated assumption). -/
def Reads {Out : Type} (obj : Build → Name → Out) : Prop :=
  ∀ b b' m, b.src m = b'.src m → b.names = b'.names → b.extra = b'.extra →
    (∀ n ∈ b.names, n ≠ m → (b.src n).iface = (b'.src n).iface ∧
      (b.src n).bodyOpaque = (b'.src n).bodyOpaque ∧
      ((b.src n).bodyOpaque = false → (b.src n).bodies = (b'.src n).bodies)) →
    obj b m = obj b' m

theorem contrib_eq (s t : Src) (h : contrib s = contrib t) :
    s.iface = t.iface ∧ s.bodyOpaque = t.bodyOpaque ∧ (s.bodyOpaque = false → s.bodies = t.bodies) := by
  unfold contrib at h
  cases hs : s.bodyOpaque <;> cases ht : t.bodyOpaque <;> simp [hs, ht] at h ⊢ <;> simp_all

theorem map_filter_eq {β : Type} (f : Name → β) (g : Name → β) (l : List Name) (m : Name)
    (h : (l.filter (· ≠ m)).map f = (l.filter (· ≠ m)).map g) :
    ∀ n ∈ l, n ≠ m → f n = g n := by
  intro n hn hne
  have hmem : n ∈ l.filter (· ≠ m) := List.mem_filter.mpr ⟨hn, by simpa using hne⟩
  exact (List.map_inj_left.mp h) n hmem

/-- Soundness: equal pre-lowering keys ⇒ identical objects. -/
theorem prelower_key_sound {Out : Type} (obj : Build → Name → Out) (hr : Reads obj)
    (b b' : Build) (m : Name) (hk : key b m = key b' m) : obj b m = obj b' m := by
  unfold key at hk
  simp only [Prod.mk.injEq] at hk
  obtain ⟨hsrc, hnames, hdeps, hextra⟩ := hk
  unfold Reads at hr
  apply hr b b' m hsrc hnames hextra
  intro n hn hne
  have hdeps' : (b.names.filter (· ≠ m)).map (fun n => contrib (b.src n)) =
      (b.names.filter (· ≠ m)).map (fun n => contrib (b'.src n)) := by
    rw [hdeps, hnames]
  exact contrib_eq _ _ (map_filter_eq _ _ b.names m hdeps' n hn hne)

/-- Gap cross_module_impl_set: an `impl`/`extend` header is an interface line,
    so adding one in any other build module changes m's key. -/
theorem impl_header_change_changes_key (b : Build) (m n : Name) (hn : n ∈ b.names)
    (hne : n ≠ m) (s' : Src) (hif : s'.iface ≠ (b.src n).iface) :
    key b m ≠ key { b with src := fun x => if x = n then s' else b.src x } m := by
  intro hk
  unfold key at hk
  simp only [Prod.mk.injEq] at hk
  obtain ⟨_, _, hdeps, _⟩ := hk
  have := map_filter_eq _ _ b.names m hdeps n hn hne
  have h2 := (contrib_eq _ _ this).1
  simp at h2
  exact hif h2.symm

/-- Gap inline_const_body: a body that can be copied (non-opaque module) is in the key. -/
theorem copyable_body_change_changes_key (b : Build) (m n : Name) (hn : n ∈ b.names)
    (hne : n ≠ m) (hop : (b.src n).bodyOpaque = false) (s' : Src)
    (hb : s'.bodies ≠ (b.src n).bodies) :
    key b m ≠ key { b with src := fun x => if x = n then s' else b.src x } m := by
  intro hk
  unfold key at hk
  simp only [Prod.mk.injEq] at hk
  obtain ⟨_, _, hdeps, _⟩ := hk
  have := map_filter_eq _ _ b.names m hdeps n hn hne
  have h := contrib_eq _ _ this
  simp at h
  exact hb (h.2.2 hop).symm

/-- Gap resolution_new_probe: a new module (e.g. a file that starts shadowing
    a name) changes the module set, hence every key. -/
theorem new_module_changes_key (b : Build) (m n : Name) (hnew : n ∉ b.names) :
    key b m ≠ key { b with names := n :: b.names } m := by
  intro hk
  unfold key at hk
  simp only [Prod.mk.injEq] at hk
  obtain ⟨_, hnames, _, _⟩ := hk
  have : n ∈ b.names := by rw [hnames]; exact List.mem_cons_self ..
  exact hnew this

end PrelowerKeyV1
