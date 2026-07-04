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

inductive Abi where
  | ilp32d
  | lp64d
  deriving DecidableEq, Repr

inductive Mmu where
  | sv32
  | sv39
  deriving DecidableEq, Repr

inductive FormalGate where
  | rvfiSby
  deriving DecidableEq, Repr

structure ProductProfile where
  lane : Lane
  productLevel : String
  configurationProfile : String
  abi : Abi
  mmu : Mmu
  maxLuts : Nat
  targetMhz : Nat
  formalGate : FormalGate
  deriving Repr

def profile : Lane → ProductProfile
  | Lane.rv32 =>
      { lane := Lane.rv32, productLevel := "linux-rtl",
        configurationProfile := "qemu-virt+fpga-board", abi := Abi.ilp32d,
        mmu := Mmu.sv32, maxLuts := 25000, targetMhz := 50,
        formalGate := FormalGate.rvfiSby }
  | Lane.rv64 =>
      { lane := Lane.rv64, productLevel := "linux-rtl",
        configurationProfile := "qemu-virt+fpga-board", abi := Abi.lp64d,
        mmu := Mmu.sv39, maxLuts := 45000, targetMhz := 50,
        formalGate := FormalGate.rvfiSby }

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
