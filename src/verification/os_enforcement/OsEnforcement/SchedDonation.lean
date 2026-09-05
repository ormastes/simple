/-
  OsEnforcement.SchedDonation — pure model of the SimpleOS scheduling-context
  donation invariant (master plan §21.3): an L4/MCS budget donated to a passive
  server is always RETURNED to the client or CANCELLED — never leaked or lost.

  Source of truth:
    IPC / scheduler design (scheduling-context donation, seL4-MCS style)
    master plan §21.3 — "scheduling-context donation is returned or cancelled".

  Real semantics being modelled
  =============================
  When a client makes a call into a passive server, it DONATES its scheduling
  budget so the server can run on the client's time. Modelled state:
    * clientBudget   — budget currently held by the client
    * serverBorrowed — budget currently lent to the server
    * returned       — whether the donation has been settled
  Operations:
    * donate   — move the client's budget to the server
    * complete — server finishes: return the borrowed budget to the client
    * cancel   — call aborted: return the borrowed budget, mark settled
  The key safety property is conservation: no operation creates or destroys
  budget, so a donation is always fully recoverable. Core Lean 4 only
  (List/Nat/Bool, no Mathlib).

  Headline theorems (SPipe manual layer):
    OsEnforcement.donation_returned_on_complete  (SD1)
    OsEnforcement.donation_returned_on_cancel    (SD2)
    OsEnforcement.no_budget_leak                 (SD3)
  Gate: `cd src/verification/os_enforcement && lake build`.
-/

namespace OsEnforcement

-- ============================================================
-- § 1  Model — donation state and operations
-- ============================================================

/-- Scheduling-context donation state. -/
structure Donation where
  clientBudget   : Nat
  serverBorrowed : Nat
  returned       : Bool
  deriving Repr, DecidableEq

/-- `donate` — move the client's whole budget to the server. -/
def donate (d : Donation) : Donation :=
  { clientBudget := 0,
    serverBorrowed := d.serverBorrowed + d.clientBudget,
    returned := d.returned }

/-- `complete` — the server finished: return the borrowed budget to the client. -/
def complete (d : Donation) : Donation :=
  { clientBudget := d.clientBudget + d.serverBorrowed,
    serverBorrowed := 0,
    returned := true }

/-- `cancel` — the call aborted: return the borrowed budget and mark settled. -/
def cancel (d : Donation) : Donation :=
  { clientBudget := d.clientBudget + d.serverBorrowed,
    serverBorrowed := 0,
    returned := true }

/-- Total budget in the system (client + server). -/
def total (d : Donation) : Nat := d.clientBudget + d.serverBorrowed

-- ============================================================
-- § 2  The donation invariants — SD1 .. SD3
-- ============================================================

/-- SD1 — donation_returned_on_complete:
    starting from a state where the server holds no prior loan, after `donate`
    then `complete` the client budget is exactly the original — fully returned. -/
theorem donation_returned_on_complete (d : Donation) (h : d.serverBorrowed = 0) :
    (complete (donate d)).clientBudget = d.clientBudget := by
  simp [complete, donate, h]

/-- SD2 — donation_returned_on_cancel:
    likewise, after `donate` then `cancel` the client budget is exactly the
    original — cancel also returns the donation. -/
theorem donation_returned_on_cancel (d : Donation) (h : d.serverBorrowed = 0) :
    (cancel (donate d)).clientBudget = d.clientBudget := by
  simp [cancel, donate, h]

/-- SD3 — no_budget_leak:
    total budget (client + server) is invariant across every operation — nothing
    is created or destroyed (conservation). -/
theorem no_budget_leak (d : Donation) :
    total (donate d) = total d
      ∧ total (complete d) = total d
      ∧ total (cancel d) = total d := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [total, donate, complete, cancel] <;> omega

-- Axiom audit (must report no sorryAx)
#print axioms donation_returned_on_complete
#print axioms no_budget_leak

end OsEnforcement
