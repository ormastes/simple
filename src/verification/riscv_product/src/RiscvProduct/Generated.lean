/-!
# RISC-V Product Profile Generated Model

GENERATED-OWNED: this file is the regeneration boundary for the Simple-level
RISC-V product profile model. Regeneration may replace this file. Keep
additional constraints and proofs in `RiscvProduct.Constraints`.

Before changing the generated surface, read
`src/verification/riscv_product/GENERATED_CONTRACT.md`.
-/

namespace RiscvProduct

inductive Lane where
  | rv32
  | rv64
  deriving DecidableEq, Repr

/-- ABI of a lane. `ilp32`/`lp64` are soft-float; `ilp32d`/`lp64d` are hard-float
and require an F/D unit the generated cores do not have. -/
inductive Abi where
  | ilp32
  | lp64
  | ilp32d
  | lp64d
  deriving DecidableEq, Repr

inductive Mmu where
  | sv32
  | sv39
  deriving DecidableEq, Repr

/-- The designated formal-verification flow for a lane. -/
inductive FormalFlow where
  | rvfiSby
  deriving DecidableEq, Repr

/-- The *result* of the formal gate. `placeholderRejected` means the lane's RTL is
a placeholder with no semantic RVFI, so the flow refuses to certify it. -/
inductive FormalGate where
  | rvfiSby
  | placeholderRejected
  deriving DecidableEq, Repr

/-- Product readiness of a lane. -/
inductive Readiness where
  | contractNotReady
  | productionReady
  deriving DecidableEq, Repr

structure ProductProfile where
  lane : Lane
  productLevel : String
  configurationProfile : String
  abi : Abi
  mmu : Mmu
  maxLuts : Nat
  targetMhz : Nat
  readiness : Readiness
  formalFlow : FormalFlow
  formalGate : FormalGate
  deriving Repr

/-- True when the ABI requires hardware floating point. -/
def Abi.isHardFloat : Abi → Bool
  | Abi.ilp32d => true
  | Abi.lp64d => true
  | Abi.ilp32 => false
  | Abi.lp64 => false

def profile : Lane → ProductProfile
  | Lane.rv32 =>
      { lane := Lane.rv32, productLevel := "linux-rtl",
        configurationProfile := "qemu-virt+fpga-board", abi := Abi.ilp32,
        mmu := Mmu.sv32, maxLuts := 25000, targetMhz := 50,
        readiness := Readiness.contractNotReady,
        formalFlow := FormalFlow.rvfiSby,
        formalGate := FormalGate.placeholderRejected }
  | Lane.rv64 =>
      { lane := Lane.rv64, productLevel := "linux-rtl",
        configurationProfile := "qemu-virt+fpga-board", abi := Abi.lp64,
        mmu := Mmu.sv39, maxLuts := 45000, targetMhz := 50,
        readiness := Readiness.contractNotReady,
        formalFlow := FormalFlow.rvfiSby,
        formalGate := FormalGate.placeholderRejected }

def withProductMetadata
    (p : ProductProfile)
    (productLevel configurationProfile : String) : ProductProfile :=
  { p with productLevel := productLevel, configurationProfile := configurationProfile }

def withBudgets
    (p : ProductProfile)
    (maxLuts targetMhz : Nat) : ProductProfile :=
  { p with maxLuts := maxLuts, targetMhz := targetMhz }

def nextLane : Lane → Lane
  | Lane.rv32 => Lane.rv64
  | Lane.rv64 => Lane.rv32

def servedWithinTwo (start target : Lane) : Prop :=
  nextLane start = target ∨ nextLane (nextLane start) = target

structure ResourceState where
  owner : Option Lane
  deriving Repr

def acquire (s : ResourceState) (l : Lane) : Option ResourceState :=
  match s.owner with
  | none => some { owner := some l }
  | some _ => none

def release (s : ResourceState) (l : Lane) : ResourceState :=
  match s.owner with
  | some owner => if owner = l then { owner := none } else s
  | none => s

end RiscvProduct
