/-! Exact bounded FIFO semantics for the kernel process queue. -/
namespace ActorChannel.ProcessQueueExact

structure Message where
  data : List UInt8
  attached : UInt64
  deriving DecidableEq, Repr

structure Queue where
  capacity : Nat
  messages : List Message
  closedSend : Bool
  deriving DecidableEq, Repr

inductive SendResult where | sent | again | pipe
  deriving DecidableEq, Repr

inductive RecvResult where | message (value : Message) | again | eof
  deriving DecidableEq, Repr

def send (q : Queue) (m : Message) : SendResult × Queue :=
  if q.closedSend then (.pipe, q)
  else if q.messages.length ≥ q.capacity then (.again, q)
  else (.sent, { q with messages := q.messages ++ [m] })

def recv (q : Queue) : RecvResult × Queue :=
  match q.messages with
  | [] => if q.closedSend then (.eof, q) else (.again, q)
  | m :: rest => (.message m, { q with messages := rest })

def closeSend (q : Queue) : Queue := { q with closedSend := true }

theorem two_send_fifo (m1 m2 : Message) :
    let q0 : Queue := { capacity := 2, messages := [], closedSend := false }
    let q1 := (send q0 m1).2
    let q2 := (send q1 m2).2
    (recv q2).1 = .message m1 ∧
      (recv (recv q2).2).1 = .message m2 := by
  simp [send, recv]

theorem full_queue_backpressure (m1 m2 m3 : Message) :
    let q0 : Queue := { capacity := 2, messages := [], closedSend := false }
    let q1 := (send q0 m1).2
    let q2 := (send q1 m2).2
    send q2 m3 = (.again, q2) := by
  simp [send]

theorem close_drains_then_eof (m : Message) :
    let q0 : Queue := { capacity := 1, messages := [], closedSend := false }
    let q1 := closeSend (send q0 m).2
    (recv q1).1 = .message m ∧
      (recv (recv q1).2).1 = .eof := by
  simp [send, closeSend, recv]

theorem close_rejects_send (q : Queue) (m : Message) :
    send (closeSend q) m = (.pipe, closeSend q) := by
  simp [send, closeSend]

theorem process_queue_refinement_bundle :
    (∀ m1 m2 : Message,
      let q0 : Queue := { capacity := 2, messages := [], closedSend := false }
      let q1 := (send q0 m1).2
      let q2 := (send q1 m2).2
      (recv q2).1 = .message m1 ∧
        (recv (recv q2).2).1 = .message m2) ∧
    (∀ m1 m2 m3 : Message,
      let q0 : Queue := { capacity := 2, messages := [], closedSend := false }
      let q1 := (send q0 m1).2
      let q2 := (send q1 m2).2
      send q2 m3 = (.again, q2)) ∧
    (∀ m : Message,
      let q0 : Queue := { capacity := 1, messages := [], closedSend := false }
      let q1 := closeSend (send q0 m).2
      (recv q1).1 = .message m ∧
        (recv (recv q1).2).1 = .eof) ∧
    (∀ (q : Queue) (m : Message),
      send (closeSend q) m = (.pipe, closeSend q)) := by
  exact ⟨two_send_fifo, full_queue_backpressure,
    close_drains_then_eof, close_rejects_send⟩

#print axioms process_queue_refinement_bundle

end ActorChannel.ProcessQueueExact
