/-!
# Exact green-channel close/drain projection

Unlike the older broad ActorChannel model, this bounded bridge includes all
five product fields, notably `backpressureCount`. It is the theorem authority
for the implementation-linked close/drain FV2 slice.
-/

namespace ActorChannel.GreenCloseExact

structure Channel where
  capacity : Int
  queuedValues : List Int
  waitingTaskIds : List Int
  backpressureCount : Int
  closed : Bool
  deriving DecidableEq, Repr

structure CloseResult where
  channel : Channel
  wokenTaskIds : List Int
  deriving DecidableEq, Repr

def closeDrain (channel : Channel) : CloseResult :=
  { channel :=
      { capacity := channel.capacity
        queuedValues := channel.queuedValues
        waitingTaskIds := []
        backpressureCount := channel.backpressureCount
        closed := true }
    wokenTaskIds := channel.waitingTaskIds }

theorem close_drain_exact (channel : Channel) :
    closeDrain channel =
      { channel :=
          { capacity := channel.capacity
            queuedValues := channel.queuedValues
            waitingTaskIds := []
            backpressureCount := channel.backpressureCount
            closed := true }
        wokenTaskIds := channel.waitingTaskIds } := by
  rfl

theorem close_drain_idempotent_channel (channel : Channel) :
    (closeDrain (closeDrain channel).channel).channel =
      (closeDrain channel).channel := by
  rfl

theorem close_drain_wakes_exactly_once (channel : Channel) :
    (closeDrain (closeDrain channel).channel).wokenTaskIds = [] ∧
      (closeDrain channel).wokenTaskIds = channel.waitingTaskIds := by
  simp [closeDrain]

/-- Composite FV2 root for exact close state, idempotence, and wake behavior. -/
theorem close_drain_refinement_bundle :
    (∀ channel : Channel,
      closeDrain channel =
        { channel :=
            { capacity := channel.capacity
              queuedValues := channel.queuedValues
              waitingTaskIds := []
              backpressureCount := channel.backpressureCount
              closed := true }
          wokenTaskIds := channel.waitingTaskIds }) ∧
    (∀ channel : Channel,
      (closeDrain (closeDrain channel).channel).channel =
        (closeDrain channel).channel) ∧
    (∀ channel : Channel,
      (closeDrain (closeDrain channel).channel).wokenTaskIds = [] ∧
        (closeDrain channel).wokenTaskIds = channel.waitingTaskIds) := by
  exact ⟨close_drain_exact, close_drain_idempotent_channel,
    close_drain_wakes_exactly_once⟩

#print axioms close_drain_refinement_bundle

end ActorChannel.GreenCloseExact
