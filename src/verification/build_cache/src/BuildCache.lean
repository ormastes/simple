import Std

/-
Manual proof candidate. The source map and hashes are in ../source_bindings.json.
This is NOT source refinement. Replay must separately call the pinned Simple
functions. No proof result may be inferred before Lean and its axiom audit run.
Current owner predicates mirror service.spl/coordinator.spl at c48d5fb07cc5.
-/
namespace BuildCache

structure Identity where
  source : String
  configuration : String
  target : String
  dependencies : String
  aspects : String
  staticSelection : String
  genericBodies : String
  parser : String
  codec : String
  deriving DecidableEq, Repr

def reuse (stored requested : Identity) : Bool := decide (stored = requested)

theorem source_change_invalidates (a b : Identity) (h : a.source ≠ b.source) :
    reuse a b = false := by
  have different : a ≠ b := fun same => h (congrArg Identity.source same)
  simp [reuse, different]

theorem generic_body_change_invalidates (a b : Identity)
    (h : a.genericBodies ≠ b.genericBodies) : reuse a b = false := by
  have different : a ≠ b := fun same => h (congrArg Identity.genericBodies same)
  simp [reuse, different]

/- Header membership is evidence from the actual admitted Git tree, not mtime.
   Source bytes, producer/configuration and selected roots are bound by caller
   evidence. No theorem here proves Git object parsing or collision resistance. -/
def headerAdmitted (member sourceEqual producerEqual rootsEqual : Bool)
    (_sourceMtime _headerMtime : Nat) : Bool :=
  member && sourceEqual && producerEqual && rootsEqual

theorem newer_header_cannot_mask_change (m p r : Bool) (s h : Nat) :
    headerAdmitted m false p r s h = false := by simp [headerAdmitted]

theorem absent_committed_header_rejected (s p r : Bool) (a b : Nat) :
    headerAdmitted false s p r a b = false := by simp [headerAdmitted]

structure Completion where
  requestedAction : String
  resultAction : String
  ownerMatches : Bool
  compatibilityMatches : Bool
  snapshotMatches : Bool
  resultWellFormed : Bool
  deriving Repr

/- Actual c48 service.spl complete gate, with cancellation and entry selection
   already satisfied. protocol.spl validates internal frame action IDs only. -/
def currentCompletionGate (c : Completion) : Bool :=
  c.ownerMatches && c.compatibilityMatches && c.snapshotMatches && c.resultWellFormed

def requiredCompletionGate (c : Completion) : Bool :=
  decide (c.requestedAction = c.resultAction) && currentCompletionGate c

def wrongAction : Completion := ⟨"A", "B", true, true, true, true⟩

theorem current_cross_action_counterexample : currentCompletionGate wrongAction = true := by decide
theorem required_cross_action_rejection : requiredCompletionGate wrongAction = false := by decide

inductive Phase where
  | queued | leased | completed | rejected
  deriving DecidableEq, Repr

def currentForeignCompletion (p : Phase) : Phase :=
  if p = .leased then .rejected else p

def ownerCanComplete (p : Phase) : Bool := decide (p = .leased)

theorem current_foreign_owner_poison :
    ownerCanComplete (currentForeignCompletion .leased) = false := by decide

/- Single owner transfer: models only one serialized coordinator instance.
   Independent instances are a concrete counterexample to global deduplication.
   The source adapter must prove that every build/test caller uses this owner. -/
structure Flight where
  active : List Nat
  fence : Nat
  published : Bool
  deriving DecidableEq, Repr

def claim (s : Flight) (owner : Nat) : Flight :=
  if s.active = [] ∧ s.published = false then {s with active := [owner]} else s

def safe (s : Flight) : Prop := s.active.length ≤ 1

theorem claim_preserves_singleflight (s : Flight) (owner : Nat) (h : safe s) :
    safe (claim s owner) := by
  unfold claim
  split
  · simp [safe]
  · exact h

def publish (s : Flight) (owner fence : Nat) (complete sameGeneration : Bool) : Flight :=
  if s.active = [owner] ∧ s.fence = fence ∧ complete = true ∧ sameGeneration = true
  then {s with active := [], published := true} else s

theorem mixed_generation_cannot_publish (s : Flight) (owner fence : Nat) :
    publish s owner fence true false = s := by simp [publish]

theorem stale_fence_cannot_publish (s : Flight) (owner fence : Nat)
    (h : s.fence ≠ fence) : publish s owner fence true true = s := by simp [publish, h]

/- deadOwner is a trusted provider observation of the owner instance, not a
   PID number reused by another process and not a timeout alone. Reclaim bumps
   the fence before any retry. Actual service lacks this transition today. -/
def reclaimRequired (s : Flight) (owner fence : Nat) (deadOwner : Bool) : Flight :=
  if s.active = [owner] ∧ s.fence = fence ∧ deadOwner = true
  then {s with active := [], fence := s.fence + 1} else s

theorem timeout_without_death_cannot_reclaim (s : Flight) (owner fence : Nat) :
    reclaimRequired s owner fence false = s := by simp [reclaimRequired]

theorem completed_publication_blocks_rebuild (owner retry : Nat) :
    claim ⟨[], 8, true⟩ retry = ⟨[], 8, true⟩ := by simp [claim]

def initial : Flight := ⟨[], 0, false⟩

theorem disconnected_owners_duplicate :
    (claim initial 1).active.length + (claim initial 2).active.length = 2 := by decide

/- Retained flat-pool bytes, not unowned global pool indices, are the durable
   parse value. A successful complete decode reconstitutes a new local graph;
   this costs decode/bridge work, but no parse_module_body invocation. -/
structure ParseOwner where
  retained : Bool
  parseCount : Nat
  poolEpoch : Nat
  deriving DecidableEq, Repr

def parseOrReuse (s : ParseOwner) : ParseOwner :=
  if s.retained then s else {s with retained := true, parseCount := s.parseCount + 1}

theorem retained_parse_not_repeated (s : ParseOwner) (h : s.retained = true) :
    (parseOrReuse s).parseCount = s.parseCount := by simp [parseOrReuse, h]

theorem cold_then_compile_parses_once (epoch : Nat) :
    (parseOrReuse (parseOrReuse ⟨false, 0, epoch⟩)).parseCount = 1 := by simp [parseOrReuse]

def livePoolHandle (handleEpoch currentEpoch : Nat) : Bool := decide (handleEpoch = currentEpoch)

theorem reset_invalidates_unowned_handle (epoch : Nat) :
    livePoolHandle epoch (epoch + 1) = false := by simp [livePoolHandle]

def restoreComplete (validFrame : Bool) (s : ParseOwner) : Option ParseOwner :=
  if validFrame then some {s with poolEpoch := s.poolEpoch + 1} else none

theorem malformed_restore_rejected (s : ParseOwner) : restoreComplete false s = none := by rfl

theorem complete_restore_does_not_parse (s : ParseOwner) :
    (restoreComplete true s).map ParseOwner.parseCount = some s.parseCount := by rfl

/- Weighted work is separate from elapsed time. Weights must be calibrated on
   the admitted hardware/producer; no constant (including 0.1 s) is inferred. -/
structure Work where
  captureEntries : Nat
  enumeratedEntries : Nat
  hashBytes : Nat
  sourceReadBytes : Nat
  headerDecodeBytes : Nat
  parseBytes : Nat
  hirNodes : Nat
  mirNodes : Nat
  objects : Nat
  links : Nat
  startups : Nat
  schedulerSteps : Nat
  receiptEntries : Nat
  deriving Repr

def cost (w x : Work) : Nat :=
  w.captureEntries*x.captureEntries + w.enumeratedEntries*x.enumeratedEntries +
  w.hashBytes*x.hashBytes + w.sourceReadBytes*x.sourceReadBytes +
  w.headerDecodeBytes*x.headerDecodeBytes + w.parseBytes*x.parseBytes +
  w.hirNodes*x.hirNodes + w.mirNodes*x.mirNodes + w.objects*x.objects +
  w.links*x.links + w.startups*x.startups + w.schedulerSteps*x.schedulerSteps +
  w.receiptEntries*x.receiptEntries

def coldWork (entries bytes parsed hir mir targets : Nat) : Work :=
  ⟨entries, entries, bytes, bytes, 0, parsed, hir, mir, targets, 1, 1, targets, entries⟩

def warmWork (changedEntries changedBytes headerBytes parsed hir mir objects : Nat) : Work :=
  ⟨changedEntries, changedEntries, changedBytes, changedBytes, headerBytes, parsed,
    hir, mir, objects, 1, 1, objects, changedEntries⟩

theorem cold_inventory_not_per_target (n b p h m t : Nat) :
    (coldWork n b p h m t).enumeratedEntries = n := by rfl

theorem cold_parse_not_doubled_for_header (n b p h m t : Nat) :
    (coldWork n b p h m t).parseBytes = p := by rfl

theorem warm_nochange_has_no_parse_or_scan (headerBytes : Nat) :
    (warmWork 0 0 headerBytes 0 0 0 0).parseBytes = 0 ∧
    (warmWork 0 0 headerBytes 0 0 0 0).enumeratedEntries = 0 := by constructor <;> rfl

theorem cold_read_lower_bound (w : Work) (n b p h m t : Nat) :
    w.sourceReadBytes * b ≤ cost w (coldWork n b p h m t) := by
  simp only [cost, coldWork]
  omega

/- No scheduler theorem can guarantee completion while the provider never
   returns. A stuttering provider is a legal countertrace unless fairness,
   bounded finite dependencies, sufficient resources, owner-death detection,
   and eventual successful storage/compiler completion are explicit premises. -/
/- Actual artifact_service_claim_v1 visits only queued entries. Reapplying that
   owner transition cannot reclaim an entry left leased by a dead process. -/
def currentServiceClaim (phase : Phase) : Phase :=
  if phase = .queued then .leased else phase

def retryClaims : Nat → Phase → Phase
  | 0, phase => phase
  | n + 1, phase => retryClaims n (currentServiceClaim phase)

theorem unconditional_no_stall_counterexample (n : Nat) :
    retryClaims n .leased = .leased := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [retryClaims, currentServiceClaim] using ih

#print axioms source_change_invalidates
#print axioms generic_body_change_invalidates
#print axioms newer_header_cannot_mask_change
#print axioms absent_committed_header_rejected
#print axioms current_cross_action_counterexample
#print axioms required_cross_action_rejection
#print axioms current_foreign_owner_poison
#print axioms claim_preserves_singleflight
#print axioms mixed_generation_cannot_publish
#print axioms stale_fence_cannot_publish
#print axioms timeout_without_death_cannot_reclaim
#print axioms completed_publication_blocks_rebuild
#print axioms disconnected_owners_duplicate
#print axioms retained_parse_not_repeated
#print axioms cold_then_compile_parses_once
#print axioms reset_invalidates_unowned_handle
#print axioms malformed_restore_rejected
#print axioms complete_restore_does_not_parse
#print axioms cold_inventory_not_per_target
#print axioms cold_parse_not_doubled_for_header
#print axioms warm_nochange_has_no_parse_or_scan
#print axioms cold_read_lower_bound
#print axioms unconditional_no_stall_counterexample
end BuildCache
