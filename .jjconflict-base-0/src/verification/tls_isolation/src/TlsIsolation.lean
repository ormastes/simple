/-
  TlsIsolation -- Per-thread-local-storage independence (P2).

  Thread-local storage gives each thread its own slot for a key; a write in one
  thread must be invisible to every other thread, and to unrelated keys within
  the same thread. We model the TLS as a curried total map

        store : ThreadId → Key → Value

  and prove the isolation guarantees a TLS implementation must provide:

    * read-own:      a thread reads back exactly what it wrote to a key.
    * thread-isolation: a write to thread T1's slot is invisible when reading
                        the same key from any other thread T2 (T1 ≠ T2).
    * key-isolation: a write to key K1 is invisible when reading a different
                     key K2 in the same thread.

  All theorems are proved without `sorry` (std only, no Mathlib).
-/
namespace TlsIsolation

abbrev ThreadId := Nat
abbrev Key      := Nat
abbrev Value    := Nat

/-- Total per-thread store: every (thread, key) maps to a value. -/
structure TlsStore where
  slots : ThreadId → Key → Value

/-- Write `v` into thread `t`'s slot for key `k`; no other (thread, key) moves. -/
def tlsWrite (s : TlsStore) (t : ThreadId) (k : Key) (v : Value) : TlsStore :=
  { slots := fun t' k' => if t' = t ∧ k' = k then v else s.slots t' k' }

def tlsRead (s : TlsStore) (t : ThreadId) (k : Key) : Value := s.slots t k

/-- A thread reads back exactly what it just wrote. -/
theorem tls_read_own (s : TlsStore) (t : ThreadId) (k : Key) (v : Value) :
    tlsRead (tlsWrite s t k v) t k = v := by
  simp [tlsRead, tlsWrite]

/-- Thread isolation: a write into T1's slot is invisible to any other thread. -/
theorem tls_thread_isolated (s : TlsStore) (t1 t2 : ThreadId) (k : Key) (v : Value)
    (h : t1 ≠ t2) : tlsRead (tlsWrite s t1 k v) t2 k = tlsRead s t2 k := by
  simp only [tlsRead, tlsWrite]
  have hne : t2 ≠ t1 := fun e => h e.symm
  simp [hne]

/-- Key isolation: a write to K1 is invisible when reading a different key K2. -/
theorem tls_key_isolated (s : TlsStore) (t : ThreadId) (k1 k2 : Key) (v : Value)
    (h : k1 ≠ k2) : tlsRead (tlsWrite s t k1 v) t k2 = tlsRead s t k2 := by
  simp only [tlsRead, tlsWrite]
  have hne : k2 ≠ k1 := fun e => h e.symm
  simp [hne]

/-- Writes to distinct threads commute: cross-thread writes never interfere, so
    the final store is order-independent. -/
theorem tls_writes_commute (s : TlsStore) (t1 t2 : ThreadId) (k1 k2 : Key)
    (v1 v2 : Value) (h : t1 ≠ t2) (tq : ThreadId) (kq : Key) :
    tlsRead (tlsWrite (tlsWrite s t1 k1 v1) t2 k2 v2) tq kq
      = tlsRead (tlsWrite (tlsWrite s t2 k2 v2) t1 k1 v1) tq kq := by
  simp only [tlsRead, tlsWrite]
  have hs : t2 ≠ t1 := fun e => h e.symm
  by_cases hA : tq = t1 ∧ kq = k1
  · by_cases hB : tq = t2 ∧ kq = k2
    · exact absurd (hA.1 ▸ hB.1 : t1 = t2) h
    · simp [hA, hB, h, hs]
  · by_cases hB : tq = t2 ∧ kq = k2
    · simp [hA, hB, h, hs]
    · simp [hA, hB]

end TlsIsolation
