/-
  MirRegallocTv — DO-333 translation-validation soundness for REGISTER ALLOCATION
  modelled as a register RENAMING.

  Companion to `src/verification/mir_opt_tv` (constant-fold/copy-prop TV) and
  `src/verification/mir_dce_tv`. This project targets the next codegen pass in
  the certification plan: register allocation. Following the same
  translation-validation (TV) strategy, we model a per-compile checker
  `validate : (VReg → PReg) → Mir → Reg → Bool` and prove that ANY allocation it
  accepts is semantics-preserving.

  WHAT A REGALLOC IS, IN THIS MODEL
  ---------------------------------
  A register allocation is a RENAMING `ρ : VReg → PReg` mapping every virtual
  register used by the straight-line MIR fragment to a physical register. Both
  VReg and PReg are `Nat` (`Reg := Nat`); `ρ` relocates the program's registers.
  The renamed program `renameProg ρ p` is the *allocated* code the backend emits.

  THE THEOREM (semantic preservation)
  -----------------------------------
  If `ρ` is INJECTIVE ON THE LIVE SET of the program — the set of registers the
  program mentions, plus the observed `result` register — then no two live vregs
  collide on one preg, and for EVERY input register file the allocated program,
  observed at `ρ result`, computes exactly what the original program computes at
  `result`. The two register files are related through `ρ` by an `Agree`
  relation: `env' (ρ r) = env r` for every live `r`. `Agree` on the inputs is the
  hypothesis; `Agree` on the outputs (hence equality at `result`) is the
  conclusion.

  Injectivity on the live set is EXACTLY the property that fails when a real
  allocator makes an unsound choice (two simultaneously-live vregs sharing one
  preg): the second definition clobbers the first. Section 8 exhibits precisely
  that failure and proves the validator rejects it AND that it corrupts the
  result.

  MODELLED (in scope):
    * The straight-line MIR fragment of `mir_opt_tv`: `List Instr` over registers
      (`Nat`), values are FAITHFUL 64-bit machine words (`BitVec 64`, wrapping
      `+`). Instructions: `const dst v`, `add dst a b`, `copy dst src`.
    * A structural state-transformer semantics `eval : Mir → Env → Env`.
    * The renaming `renameProg`, the live set `liveSet`, and the injective-on-live
      validator `validate`.

  OUT OF SCOPE (deferred; NOT assumed sound here):
    * SPILLING (materialising vregs to memory when pregs run out) — this model has
      unboundedly many pregs and never spills.
    * COALESCING / move elimination (deleting `copy` when src and dst share a
      preg) — `renameProg` preserves instruction shape one-for-one.
    * NON-INJECTIVE allocation of any kind (register sharing across live ranges) —
      it is exactly what the validator rejects. We prove injective RENAMING sound;
      we do not prove any sound-sharing (liveness-interference) allocator.
    * Control flow, calls, memory, and the interpreter execution path.

  All theorems are proved with the Lean core library only (no Mathlib) and with
  no proof-trust bypasses — the repo's `check-lean-proofs.shs` TRUST_RE gate must
  find nothing. Adversarial disproofs use kernel `decide` (NOT `native_decide`,
  which would add the `ofReduceBool` axiom).
-/
namespace MirRegallocTv

/-! ## 1. Syntax of the MIR fragment -/

/-- A register (virtual or physical) is identified by a natural number. -/
abbrev Reg : Type := Nat

/-- Machine values are 64-bit words. `+` on `BitVec 64` wraps modulo 2^64,
    faithfully modelling the backend's overflow behaviour. -/
abbrev Val : Type := BitVec 64

/-- Straight-line MIR instructions. -/
inductive Instr where
  /-- `const dst v` : write the literal `v` into register `dst`. -/
  | const : Reg → Val → Instr
  /-- `add dst a b` : `dst := a + b`. -/
  | add   : Reg → Reg → Reg → Instr
  /-- `copy dst src` : `dst := src`. -/
  | copy  : Reg → Reg → Instr
  deriving DecidableEq

/-- A MIR fragment is a straight-line list of instructions. -/
abbrev Mir : Type := List Instr

/-! ## 2. Concrete semantics -/

/-- A register file maps every register to its current value. -/
abbrev Env : Type := Reg → Val

/-- Point update of a register file. -/
def upd (env : Env) (r : Reg) (v : Val) : Env :=
  fun x => if x = r then v else env x

/-- One-step concrete execution of a single instruction. -/
def evalInstr (env : Env) (i : Instr) : Env :=
  match i with
  | .const d v => upd env d v
  | .add d a b => upd env d (env a + env b)
  | .copy d s  => upd env d (env s)

/-- Whole-fragment semantics: structural state transformer, left-to-right. -/
def eval : Mir → Env → Env
  | [],      env => env
  | i :: is, env => eval is (evalInstr env i)

/-! ## 3. Register renaming (the allocation) -/

/-- Rename every register mentioned by an instruction through `ρ`. -/
def renameInstr (ρ : Reg → Reg) : Instr → Instr
  | .const d v => .const (ρ d) v
  | .add d a b => .add (ρ d) (ρ a) (ρ b)
  | .copy d s  => .copy (ρ d) (ρ s)

/-- Rename a whole fragment: this is the *allocated* code. -/
def renameProg (ρ : Reg → Reg) : Mir → Mir
  | []      => []
  | i :: is => renameInstr ρ i :: renameProg ρ is

/-! ## 4. Live set: the registers the program observes

    A sound over-approximation of dataflow liveness: every register the program
    mentions (each instruction's def and uses), together with the observed
    `result` register. Injectivity is required only on THIS set — the theorem
    never constrains `ρ` on registers the program does not touch. -/

/-- Registers mentioned by one instruction (def first, then uses). -/
def instrRegs : Instr → List Reg
  | .const d _ => [d]
  | .add d a b => [d, a, b]
  | .copy d s  => [d, s]

/-- All registers mentioned by the fragment. -/
def progRegs : Mir → List Reg
  | []      => []
  | i :: is => instrRegs i ++ progRegs is

/-- The live set: program registers plus the observed result register. -/
def liveSet (p : Mir) (result : Reg) : List Reg := result :: progRegs p

/-- Every register of an instruction that occurs in `p` is in `progRegs p`. -/
theorem instrRegs_subset_progRegs (p : Mir) (i : Instr) (hi : i ∈ p)
    (r : Reg) (hr : r ∈ instrRegs i) : r ∈ progRegs p := by
  induction p with
  | nil => cases hi
  | cons j js ih =>
    rcases List.mem_cons.mp hi with h | h
    · subst h; exact List.mem_append.mpr (Or.inl hr)
    · exact List.mem_append.mpr (Or.inr (ih h))

/-! ## 5. The state relation and the injectivity check -/

/-- Two register files agree through `ρ` on a set `S`: the physical register
    `ρ r` holds the virtual register `r`'s value, for every live `r`. -/
def Agree (ρ : Reg → Reg) (S : List Reg) (env env' : Env) : Prop :=
  ∀ r ∈ S, env' (ρ r) = env r

/-- `ρ` is injective on the register list `S` (no two live vregs share a preg). -/
def InjOn (ρ : Reg → Reg) (S : List Reg) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ρ a = ρ b → a = b

/-- Decidable Boolean form of `InjOn`, over the finite live set — this is what the
    validator actually runs. -/
def injOnB (ρ : Reg → Reg) (S : List Reg) : Bool :=
  S.all (fun a => S.all (fun b => (ρ a != ρ b) || (a == b)))

/-- The Boolean check implies the propositional injectivity. -/
theorem injOnB_sound (ρ : Reg → Reg) (S : List Reg)
    (h : injOnB ρ S = true) : InjOn ρ S := by
  intro a ha b hb hab
  simp only [injOnB, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at h
  rcases h a ha b hb with hne | heq
  · exact absurd hab hne
  · exact heq

/-! ## 6. The translation validator -/

/-- The register-allocation validator: accept `ρ` for `(p, result)` iff `ρ` is
    injective on the live set (program registers plus the observed result). -/
def validate (ρ : Reg → Reg) (p : Mir) (result : Reg) : Bool :=
  injOnB ρ (liveSet p result)

/-! ## 7. Soundness -/

/-- One renamed step preserves `Agree` on the live set, provided `ρ` is injective
    there and the instruction's registers are all live. The def register `d` is
    live (it heads `instrRegs`), so injectivity guarantees writing `ρ d` cannot
    clobber `ρ r` for any other live `r`. -/
theorem agree_step (ρ : Reg → Reg) (S : List Reg) (hinj : InjOn ρ S)
    (i : Instr) (hsub : ∀ r ∈ instrRegs i, r ∈ S)
    (env env' : Env) (hag : Agree ρ S env env') :
    Agree ρ S (evalInstr env i) (evalInstr env' (renameInstr ρ i)) := by
  intro r hr
  cases i with
  | const d v =>
    have hd : d ∈ S := hsub d (by simp [instrRegs])
    show (upd env' (ρ d) v) (ρ r) = (upd env d v) r
    by_cases hrd : r = d
    · subst hrd; simp [upd]
    · have hne : ρ r ≠ ρ d := fun heq => hrd (hinj r hr d hd heq)
      simp [upd, hrd, hne]; exact hag r hr
  | add d a b =>
    have hd : d ∈ S := hsub d (by simp [instrRegs])
    have ha : a ∈ S := hsub a (by simp [instrRegs])
    have hb : b ∈ S := hsub b (by simp [instrRegs])
    show (upd env' (ρ d) (env' (ρ a) + env' (ρ b))) (ρ r) = (upd env d (env a + env b)) r
    by_cases hrd : r = d
    · subst hrd; simp [upd]; rw [hag a ha, hag b hb]
    · have hne : ρ r ≠ ρ d := fun heq => hrd (hinj r hr d hd heq)
      simp [upd, hrd, hne]; exact hag r hr
  | copy d s =>
    have hd : d ∈ S := hsub d (by simp [instrRegs])
    have hs : s ∈ S := hsub s (by simp [instrRegs])
    show (upd env' (ρ d) (env' (ρ s))) (ρ r) = (upd env d (env s)) r
    by_cases hrd : r = d
    · subst hrd; simp [upd]; exact hag s hs
    · have hne : ρ r ≠ ρ d := fun heq => hrd (hinj r hr d hd heq)
      simp [upd, hrd, hne]; exact hag r hr

/-- Running the original and the renamed fragment from `Agree`ing states keeps the
    states `Agree`ing on the whole live set. -/
theorem agree_eval (ρ : Reg → Reg) (S : List Reg) (hinj : InjOn ρ S) :
    ∀ (p : Mir), (∀ i ∈ p, ∀ r ∈ instrRegs i, r ∈ S) →
      ∀ env env', Agree ρ S env env' →
        Agree ρ S (eval p env) (eval (renameProg ρ p) env') := by
  intro p
  induction p with
  | nil => intro _ env env' hag; exact hag
  | cons i is ih =>
    intro hsub env env' hag
    have hstep : Agree ρ S (evalInstr env i) (evalInstr env' (renameInstr ρ i)) :=
      agree_step ρ S hinj i
        (fun r hr => hsub i List.mem_cons_self r hr) env env' hag
    have hsub' : ∀ j ∈ is, ∀ r ∈ instrRegs j, r ∈ S :=
      fun j hj r hr => hsub j (List.mem_cons_of_mem i hj) r hr
    have hrec := ih hsub' (evalInstr env i) (evalInstr env' (renameInstr ρ i)) hstep
    simpa only [eval, renameProg] using hrec

/-- **Main TV soundness theorem.** If the validator accepts allocation `ρ` for
    `(p, result)`, then for every pair of input register files related through
    `ρ` on the live set, the allocated program observed at `ρ result` computes
    exactly what the original computes at `result`. -/
theorem validate_sound (ρ : Reg → Reg) (p : Mir) (result : Reg)
    (h : validate ρ p result = true) :
    ∀ env env', Agree ρ (liveSet p result) env env' →
      eval (renameProg ρ p) env' (ρ result) = eval p env result := by
  intro env env' hag
  have hinj : InjOn ρ (liveSet p result) := injOnB_sound ρ _ h
  have hsub : ∀ i ∈ p, ∀ r ∈ instrRegs i, r ∈ liveSet p result := by
    intro i hi r hr
    exact List.mem_cons_of_mem result (instrRegs_subset_progRegs p i hi r hr)
  have hres : result ∈ liveSet p result := List.mem_cons_self
  have hfinal := agree_eval ρ (liveSet p result) hinj p hsub env env' hag
  exact hfinal result hres

/-! ## 8. Non-vacuity and adversarial disproof (plan acceptance criteria)

    Two concrete injective allocations that VALIDATE and PRESERVE (non-vacuity),
    and one non-injective allocation that is REJECTED and CORRUPTS the result
    (adversarial). The example program computes `r2 := r0 + r1` with `r0 = 1`,
    `r1 = 2`, so `result = r2 = 3`, and both `r0` and `r1` are live at the `add`. -/

/-- `r0 := 1; r1 := 2; r2 := r0 + r1`, observed at `r2` (= 3). -/
def exProg : Mir :=
  [Instr.const 0 1, Instr.const 1 2, Instr.add 2 0 1]

/-! ### 8a. Non-vacuity via the IDENTITY allocation -/

/-- Identity allocation. -/
def idρ : Reg → Reg := fun r => r

theorem id_validates : validate idρ exProg 2 = true := by decide

/-- Renaming by the identity is a no-op on the program. -/
theorem renameProg_id : renameProg idρ exProg = exProg := by decide

/-- The identity allocation preserves the result — derived END-TO-END through the
    main theorem (with `env' = env`, `Agree` holds reflexively). -/
theorem id_preserves (env : Env) :
    eval (renameProg idρ exProg) env (idρ 2) = eval exProg env 2 :=
  validate_sound idρ exProg 2 id_validates env env (by intro r _; rfl)

/-! ### 8b. Non-vacuity via a genuine RELOCATING allocation `ρ(r) = r + 10` -/

/-- A real (non-identity) injective allocation: shift every register up by 10.
    Injective everywhere, hence injective on any live set. -/
def shiftρ : Reg → Reg := fun r => r + 10

theorem shift_validates : validate shiftρ exProg 2 = true := by decide

/-- The relocated program is literally different code (pregs 10, 11, 12). -/
theorem shift_is_real_relocation :
    renameProg shiftρ exProg
      = [Instr.const 10 1, Instr.const 11 2, Instr.add 12 10 11] := by decide

/-- The relocating allocation preserves the result — derived END-TO-END through
    the main theorem; observed at the RELOCATED result register `ρ 2 = 12`. The
    two input files are related through `ρ` (here both all-zero, which `Agree`s
    for any `ρ`), and the theorem transports that to equality at the output. -/
theorem shift_preserves :
    eval (renameProg shiftρ exProg) (fun _ => 0) (shiftρ 2)
      = eval exProg (fun _ => 0) 2 :=
  validate_sound shiftρ exProg 2 shift_validates (fun _ => 0) (fun _ => 0)
    (by intro r _; rfl)

/-- Concrete cross-check that `shift_preserves` is non-trivial: on the all-zero
    input the relocated program's preg 12 holds 3, the original's r2 holds 3. -/
theorem shift_preserves_concrete :
    eval (renameProg shiftρ exProg) (fun _ => 0) 12 = 3
      ∧ eval exProg (fun _ => 0) 2 = 3 := by decide

/-! ### 8c. Adversarial: a NON-INJECTIVE allocation that collides two live vregs -/

/-- Bad allocation: send `r1 ↦ p0` while `r0 ↦ p0` too (`ρ 0 = 0`, `ρ 1 = 0`).
    `r0` and `r1` are BOTH live at `r2 := r0 + r1`, so they must not share a preg.
    This is exactly the interference an allocator must avoid. -/
def badρ : Reg → Reg := fun r => if r = 1 then 0 else r

/-- The validator REJECTS the colliding allocation (it is not injective on the
    live set: `ρ 0 = ρ 1 = 0` but `0 ≠ 1`). -/
theorem adv_rejected : validate badρ exProg 2 = false := by decide

/-- …and rejection is warranted: the colliding allocation genuinely CORRUPTS the
    result. The renamed code is `p0 := 1; p0 := 2; p2 := p0 + p0`, so `p2 = 4`
    (the second def clobbered the first), whereas the source computes `r2 = 3`.
    Observed at the renamed result `ρ 2 = 2`. -/
theorem adv_corrupts :
    eval (renameProg badρ exProg) (fun _ => 0) (badρ 2)
      ≠ eval exProg (fun _ => 0) 2 := by decide

/-- Pin down the corruption explicitly: the colliding allocation yields 4, not 3. -/
theorem adv_corrupt_value :
    eval (renameProg badρ exProg) (fun _ => 0) (badρ 2) = 4
      ∧ eval exProg (fun _ => 0) 2 = 3 := by decide

/-! ## 9. Disclosed axiom footprint (must be only the standard three). -/

#print axioms validate_sound
#print axioms id_preserves
#print axioms shift_preserves
#print axioms adv_rejected
#print axioms adv_corrupts

end MirRegallocTv
