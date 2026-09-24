/-!
Pure model for the bounded L7 three-payload proof slice.

This file intentionally models records and transitions only.  The Simple
source replay owns source-byte binding and the remaining refinement boundary.
-/

namespace ThreePayloadCompile

inductive ReadRole where
  | source
  | prior
  | initializer
  deriving DecidableEq, Repr

structure BrokerState where
  pending : List ReadRole
  trace : List ReadRole
  remainingBytes : Nat
  successfulBytes : Nat
  failed : Bool
  deriving DecidableEq, Repr

def initialBroker (hasPrior : Bool) (budget : Nat) : BrokerState :=
  { pending := if hasPrior then [.source, .prior, .initializer]
      else [.source, .initializer]
    trace := []
    remainingBytes := budget
    successfulBytes := 0
    failed := false }

def brokerStep (s : BrokerState) (outcome : Option Nat) : BrokerState :=
  if s.failed then s
  else match s.pending with
    | [] => s
    | role :: rest =>
      if s.remainingBytes = 0 then { s with failed := true }
      else match outcome with
        | none =>
          { s with pending := rest, trace := s.trace ++ [role], failed := true }
        | some n =>
          if n ≤ s.remainingBytes then
            { s with pending := rest, trace := s.trace ++ [role], remainingBytes := s.remainingBytes - n, successfulBytes := s.successfulBytes + n }
          else
            { s with pending := rest, trace := s.trace ++ [role], failed := true }

def brokerRun (hasPrior : Bool) (budget : Nat)
    (outcomes : List (Option Nat)) : BrokerState :=
  outcomes.foldl brokerStep (initialBroker hasPrior budget)

def brokerSucceeded (s : BrokerState) : Prop :=
  s.failed = false ∧ s.pending = []

structure RrEdge where
  producerKey : String
  consumerKey : String
  facet : String
  partition : String
  fingerprint : String
  manifest : String
  deriving DecidableEq, Repr, BEq, ReflBEq, LawfulBEq

def rrIdentity (e : RrEdge) : String × String × String × String :=
  (e.producerKey, e.consumerKey, e.facet, e.partition)

def rrUnique (edges : List RrEdge) : Prop :=
  (edges.map rrIdentity).Nodup

structure RrDelta where
  inserted : List RrEdge
  removed : List RrEdge
  deriving DecidableEq, Repr

def reverseDelta (old new : List RrEdge) : RrDelta :=
  { inserted := new.filter (fun edge => !(old.contains edge))
    removed := old.filter (fun edge => !(new.contains edge)) }

def applyReverseDelta (all : List RrEdge) (delta : RrDelta) : List RrEdge :=
  all.filter (fun edge => !(delta.removed.contains edge)) ++ delta.inserted

inductive RrMutationRoute where
  | refusedMissingHistory
  | staged (oldReads newReads : List RrEdge)
  deriving DecidableEq, Repr

def routeRrMutation (oldHistory : Option (List RrEdge))
    (newReads : List RrEdge) : RrMutationRoute :=
  match oldHistory with
  | none => .refusedMissingHistory
  | some oldReads => .staged oldReads newReads

structure JournalRecord where
  sequence : Nat
  action : String
  kind : String
  object : String
  manifest : String
  deriving DecidableEq, Repr

structure JournalState where
  generation : Nat
  nextSequence : Nat
  entries : List JournalRecord
  deriving DecidableEq, Repr

structure JournalPrepared where
  generation : Nat
  entryPrefix : List JournalRecord
  record : JournalRecord
  deriving DecidableEq, Repr

def journalAccept (s : JournalState) (p : JournalPrepared) : Option JournalState :=
  if p.generation != s.generation then none
  else if s.entries = p.entryPrefix ∧ s.nextSequence = p.record.sequence then
    some { generation := s.generation,
           nextSequence := s.nextSequence + 1,
           entries := s.entries ++ [p.record] }
  else if s.entries = p.entryPrefix ++ [p.record] ∧
      s.nextSequence = p.record.sequence + 1 then
    some s
  else none

structure GenerationRoots where
  summary : String
  scope : String
  forwardReads : String
  reverseReferences : String
  objects : String
  deriving DecidableEq, Repr

structure GenerationIdentity where
  generation : Nat
  manifest : String
  deriving DecidableEq, Repr, BEq, ReflBEq, LawfulBEq

structure DurableGeneration where
  identity : GenerationIdentity
  roots : GenerationRoots
  deriving DecidableEq, Repr

structure DurablePublicationState where
  active : DurableGeneration
  committedGenerations : List GenerationIdentity
  deriving DecidableEq, Repr

inductive PublicationAttemptEvent where
  | precommitRefusal
  | casConflict
  | casAcknowledged
  | casAcknowledgmentLost
  | cancellationAfterCas
  deriving DecidableEq, Repr

inductive PublicationAttemptOutcome where
  | refused (durableActive : DurableGeneration)
  | committed (candidate : GenerationIdentity) (durableActive : DurableGeneration)
  | unknown (candidate : GenerationIdentity) (durableActive : DurableGeneration)
  deriving DecidableEq, Repr

def resolvePublicationAttempt (candidate : GenerationIdentity)
    (event : PublicationAttemptEvent)
    (durable : DurablePublicationState) : PublicationAttemptOutcome :=
  match event with
  | .precommitRefusal =>
      if durable.committedGenerations.contains candidate then
        .unknown candidate durable.active
      else
        .refused durable.active
  | .casConflict =>
      if durable.committedGenerations.contains candidate then
        .unknown candidate durable.active
      else
        .refused durable.active
  | .casAcknowledged =>
      if durable.committedGenerations.contains candidate then
        .committed candidate durable.active
      else
        .unknown candidate durable.active
  | .casAcknowledgmentLost =>
      if durable.committedGenerations.contains candidate then
        .committed candidate durable.active
      else
        .unknown candidate durable.active
  | .cancellationAfterCas =>
      if durable.committedGenerations.contains candidate then
        .committed candidate durable.active
      else
        .unknown candidate durable.active

def generationRootsNonemptyShape (roots : GenerationRoots) : Prop :=
  roots.summary ≠ "" ∧ roots.scope ≠ "" ∧ roots.forwardReads ≠ "" ∧
    roots.reverseReferences ≠ "" ∧ roots.objects ≠ ""

def durableGenerationNonemptyShape (generation : DurableGeneration) : Prop :=
  generation.identity.manifest ≠ "" ∧ generationRootsNonemptyShape generation.roots

def atomicRecordSwap (expected : GenerationIdentity) (candidate : DurableGeneration)
    (durable : DurablePublicationState) : Option DurablePublicationState :=
  if durable.active.identity = expected ∧ durableGenerationNonemptyShape candidate then
    some { active := candidate
           committedGenerations := candidate.identity :: durable.committedGenerations }
  else
    none

inductive SweepDecision where
  | refused
  | retained
  | eligible
  deriving DecidableEq, Repr

def sweepDecision (snapshotEpoch currentEpoch : Nat)
    (closureComplete : Bool) (protectedObjects : List String)
    (candidate : String) : SweepDecision :=
  if snapshotEpoch != currentEpoch || !closureComplete then .refused
  else if protectedObjects.contains candidate then .retained
  else .eligible

end ThreePayloadCompile
