/-
  HashAgilityV1 — T-HA1 for the hash-algorithm registry and DigestV1
  (src/compiler/00.common/cache_contract/hash_algorithm_registry_v1.spl, #4421).
  Plan: cache_invalidation_formal_verification_2026-10-24.md §4.1 T-HA1.
  SSpec twin over the real Simple functions:
  test/00_formal_verification/compiler/hash_agility_bounded_spec.spl

  Proved: registry ids and names are unique; an unknown algorithm name or id
  is ABSENT (parse/new = none), never a match; digests of different algorithms
  are never equal and are distinct keys; a negotiated set match
  implies a shared KNOWN algorithm with equal bytes, collision resistant when
  identity is required; sets sharing no known algorithm are a miss (NO_COMMON).
  The hex charset check is a parameter `hexOk` (every theorem holds for any).
  No sorry, no axioms.
-/
namespace HashAgilityV1

structure Algo where
  id    : Nat
  name  : String
  bytes : Nat
  cr    : Bool
  deriving DecidableEq, Repr

def registry : List Algo :=
  [⟨1, "sha256", 32, true⟩, ⟨2, "blake3", 32, true⟩, ⟨3, "sha3-256", 32, true⟩,
   ⟨16, "xxh3-128", 16, false⟩, ⟨17, "xxh3-64", 8, false⟩, ⟨18, "crc32", 4, false⟩]

theorem registry_ids_unique : (registry.map Algo.id).Nodup := by decide
theorem registry_names_unique : (registry.map Algo.name).Nodup := by decide

def byId (id : Nat) : Option Algo := registry.find? (fun a => a.id == id)
def byName (n : String) : Option Algo := registry.find? (fun a => a.name == n)

structure Digest where
  algo : Nat
  hex  : String
  deriving DecidableEq, Repr

def known (id : Nat) : Bool := (byId id).isSome

def mk (hexOk : String → Nat → Bool) (id : Nat) (hex : String) : Option Digest :=
  match byId id with
  | some a => if hexOk hex a.bytes then some ⟨id, hex⟩ else none
  | none   => none

def parse (hexOk : String → Nat → Bool) (name hex : String) : Option Digest :=
  match byName name with
  | some a => mk hexOk a.id hex
  | none   => none

def text (d : Digest) : String :=
  match byId d.algo with
  | some a => a.name ++ ":" ++ d.hex
  | none   => ""

def equal (a b : Digest) : Bool := a.algo == b.algo && a.hex == b.hex && known a.algo

theorem unknown_id_absent (hexOk : String → Nat → Bool) (id : Nat) (hex : String)
    (h : byId id = none) : mk hexOk id hex = none := by
  simp [mk, h]

theorem unknown_name_absent (hexOk : String → Nat → Bool) (n hex : String)
    (h : byName n = none) : parse hexOk n hex = none := by
  simp [parse, h]

theorem equal_requires_known (a b : Digest) (h : equal a b = true) : known a.algo = true := by
  simp [equal] at h; exact h.2

theorem different_algo_never_equal (a b : Digest) (h : a.algo ≠ b.algo) : equal a b = false := by
  simp [equal, h]

theorem byId_id (id : Nat) (a : Algo) (h : byId id = some a) : a.id = id := by
  unfold byId at h
  have := List.find?_some h
  simpa using this

theorem byId_mem (id : Nat) (a : Algo) (h : byId id = some a) : a ∈ registry :=
  List.mem_of_find?_eq_some h

/-- Algorithm-namespaced keys: digests with different tags are different keys. -/
theorem different_algo_digest_ne (a b : Digest) (h : a.algo ≠ b.algo) : a ≠ b := by
  intro he; exact h (by rw [he])

def cr (id : Nat) : Bool :=
  match byId id with
  | some a => a.cr
  | none   => false

/-- First shared known algorithm for wanted digest `w` within `have`. -/
def findHave (hs : List Digest) (w : Digest) : Option Digest :=
  hs.find? (fun h => h.algo == w.algo && known h.algo)

def firstCommon (pass : Bool) (hs : List Digest) : List Digest → Option (Digest × Digest)
  | [] => none
  | w :: ws =>
    if cr w.algo = pass then
      match findHave hs w with
      | some h => some (h, w)
      | none   => firstCommon pass hs ws
    else firstCommon pass hs ws

/-- digest_set_match_v1: 1 match, 0 mismatch, -1 no common (=> miss). -/
def setMatch (hs want : List Digest) (need : Bool) : Int :=
  match firstCommon true hs want with
  | some (h, w) => if h.hex = w.hex then 1 else 0
  | none =>
    if need then -1 else
    match firstCommon false hs want with
    | some (h, w) => if h.hex = w.hex then 1 else 0
    | none        => -1

theorem firstCommon_spec (pass : Bool) (hs want : List Digest) (h w : Digest)
    (hf : firstCommon pass hs want = some (h, w)) :
    h ∈ hs ∧ w ∈ want ∧ h.algo = w.algo ∧ known h.algo = true ∧ cr w.algo = pass := by
  induction want with
  | nil => simp [firstCommon] at hf
  | cons x xs ih =>
    unfold firstCommon at hf
    by_cases hc : cr x.algo = pass
    · simp only [hc, if_true] at hf
      cases hfh : findHave hs x with
      | none =>
        rw [hfh] at hf
        obtain ⟨a, b, c, d, e⟩ := ih hf
        exact ⟨a, List.mem_cons_of_mem _ b, c, d, e⟩
      | some y =>
        rw [hfh] at hf
        simp at hf
        obtain ⟨rfl, rfl⟩ := hf
        have hm := List.mem_of_find?_eq_some hfh
        have hp := List.find?_some hfh
        simp at hp
        exact ⟨hm, List.mem_cons_self .., hp.1, hp.2, hc⟩
    · simp only [hc, if_false] at hf
      obtain ⟨a, b, c, d, e⟩ := ih hf
      exact ⟨a, List.mem_cons_of_mem _ b, c, d, e⟩

/-- A match means a shared, known algorithm with equal bytes. -/
theorem match_implies_shared_equal (hs want : List Digest) (need : Bool)
    (hm : setMatch hs want need = 1) :
    ∃ h ∈ hs, ∃ w ∈ want, h.algo = w.algo ∧ known h.algo = true ∧ h.hex = w.hex := by
  unfold setMatch at hm
  cases h1 : firstCommon true hs want with
  | some p =>
    obtain ⟨h, w⟩ := p
    rw [h1] at hm
    obtain ⟨a, b, c, d, _⟩ := firstCommon_spec _ _ _ _ _ h1
    by_cases hx : h.hex = w.hex
    · exact ⟨h, a, w, b, c, d, hx⟩
    · simp [hx] at hm
  | none =>
    rw [h1] at hm
    cases need
    · cases h2 : firstCommon false hs want with
      | some p =>
        obtain ⟨h, w⟩ := p
        rw [h2] at hm
        obtain ⟨a, b, c, d, _⟩ := firstCommon_spec _ _ _ _ _ h2
        by_cases hx : h.hex = w.hex
        · exact ⟨h, a, w, b, c, d, hx⟩
        · simp [hx] at hm
      | none => rw [h2] at hm; simp at hm
    · simp at hm

/-- With identity required, a match is on a collision-resistant algorithm. -/
theorem identity_match_collision_resistant (hs want : List Digest)
    (hm : setMatch hs want true = 1) :
    ∃ h ∈ hs, ∃ w ∈ want, h.algo = w.algo ∧ cr w.algo = true ∧ h.hex = w.hex := by
  unfold setMatch at hm
  cases h1 : firstCommon true hs want with
  | some p =>
    obtain ⟨h, w⟩ := p
    rw [h1] at hm
    obtain ⟨a, b, c, _, e⟩ := firstCommon_spec _ _ _ _ _ h1
    by_cases hx : h.hex = w.hex
    · exact ⟨h, a, w, b, c, e, hx⟩
    · simp [hx] at hm
  | none => rw [h1] at hm; simp at hm

theorem firstCommon_none_of_no_known (pass : Bool) (hs want : List Digest)
    (hk : ∀ h ∈ hs, known h.algo = false) : firstCommon pass hs want = none := by
  induction want with
  | nil => rfl
  | cons x xs ih =>
    have hnone : findHave hs x = none := by
      unfold findHave
      rw [List.find?_eq_none]
      intro h hh
      simp [hk h hh]
    unfold firstCommon
    by_cases hc : cr x.algo = pass <;> simp [hc, hnone, ih]

/-- Unknown algorithms only (e.g. a peer on a newer registry): miss, never match. -/
theorem unknown_only_is_miss (hs want : List Digest) (need : Bool)
    (hk : ∀ h ∈ hs, known h.algo = false) : setMatch hs want need = -1 := by
  unfold setMatch
  rw [firstCommon_none_of_no_known true hs want hk]
  cases need <;> simp [firstCommon_none_of_no_known false hs want hk]

end HashAgilityV1
