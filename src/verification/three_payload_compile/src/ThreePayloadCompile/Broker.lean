import ThreePayloadCompile.Model

namespace ThreePayloadCompile

example : brokerSucceeded (brokerRun false 2 [some 1, some 1]) := by
  unfold brokerSucceeded
  decide

example : brokerSucceeded
    (brokerRun true 3 [some 1, some 1, some 1]) := by
  unfold brokerSucceeded
  decide

private theorem brokerStep_roles_conserved (s : BrokerState)
    (outcome : Option Nat) :
    (brokerStep s outcome).trace.length +
        (brokerStep s outcome).pending.length =
      s.trace.length + s.pending.length := by
  cases hf : s.failed with
  | true => simp [brokerStep, hf]
  | false =>
    cases hp : s.pending with
    | nil => simp [brokerStep, hf, hp]
    | cons role rest =>
      by_cases hz : s.remainingBytes = 0
      · simp [brokerStep, hf, hp, hz]
      · cases outcome with
        | none => simp [brokerStep, hf, hp, hz] <;> omega
        | some n =>
          by_cases hn : n ≤ s.remainingBytes <;>
            simp [brokerStep, hf, hp, hz, hn] <;> omega

private theorem brokerStep_bytes_conserved (s : BrokerState)
    (outcome : Option Nat) :
    (brokerStep s outcome).successfulBytes +
        (brokerStep s outcome).remainingBytes =
      s.successfulBytes + s.remainingBytes := by
  cases hf : s.failed with
  | true => simp [brokerStep, hf]
  | false =>
    cases hp : s.pending with
    | nil => simp [brokerStep, hf, hp]
    | cons role rest =>
      by_cases hz : s.remainingBytes = 0
      · simp [brokerStep, hf, hp, hz]
      · cases outcome with
        | none => simp [brokerStep, hf, hp, hz]
        | some n =>
          by_cases hn : n ≤ s.remainingBytes
          · simp [brokerStep, hf, hp, hz, hn]
            omega
          · simp [brokerStep, hf, hp, hz, hn]

private theorem brokerFold_roles_conserved (s : BrokerState)
    (outcomes : List (Option Nat)) :
    (outcomes.foldl brokerStep s).trace.length +
        (outcomes.foldl brokerStep s).pending.length =
      s.trace.length + s.pending.length := by
  induction outcomes generalizing s with
  | nil => simp
  | cons outcome rest ih =>
    simp only [List.foldl_cons]
    rw [ih, brokerStep_roles_conserved]

private theorem brokerFold_bytes_conserved (s : BrokerState)
    (outcomes : List (Option Nat)) :
    (outcomes.foldl brokerStep s).successfulBytes +
        (outcomes.foldl brokerStep s).remainingBytes =
      s.successfulBytes + s.remainingBytes := by
  induction outcomes generalizing s with
  | nil => simp
  | cons outcome rest ih =>
    simp only [List.foldl_cons]
    rw [ih, brokerStep_bytes_conserved]

theorem broker_prefix_read_bound (hasPrior : Bool) (budget : Nat)
    (outcomes : List (Option Nat)) :
    (brokerRun hasPrior budget outcomes).trace.length ≤
      2 + (if hasPrior then 1 else 0) := by
  have h := brokerFold_roles_conserved
    (initialBroker hasPrior budget) outcomes
  cases hasPrior <;> simp [brokerRun, initialBroker] at h ⊢ <;> omega

theorem broker_success_read_count (hasPrior : Bool) (budget : Nat)
    (outcomes : List (Option Nat))
    (h : brokerSucceeded (brokerRun hasPrior budget outcomes)) :
    (brokerRun hasPrior budget outcomes).trace.length =
      2 + (if hasPrior then 1 else 0) := by
  have hc := brokerFold_roles_conserved
    (initialBroker hasPrior budget) outcomes
  rcases h with ⟨_, hpending⟩
  change (brokerRun hasPrior budget outcomes).trace.length +
      (brokerRun hasPrior budget outcomes).pending.length =
    (initialBroker hasPrior budget).trace.length +
      (initialBroker hasPrior budget).pending.length at hc
  rw [hpending] at hc
  cases hasPrior <;>
    simp [initialBroker] at hc ⊢ <;> omega

theorem broker_prefix_byte_bound (hasPrior : Bool) (budget : Nat)
    (outcomes : List (Option Nat)) :
    (brokerRun hasPrior budget outcomes).successfulBytes ≤ budget := by
  have h := brokerFold_bytes_conserved
    (initialBroker hasPrior budget) outcomes
  simp [brokerRun, initialBroker] at h ⊢
  omega

end ThreePayloadCompile
