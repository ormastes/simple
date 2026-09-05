/-
  MirIselTv — DO-333 translation-validation soundness for INSTRUCTION SELECTION
  (source MIR → a small target "machine" ISA).

  Plan: doc/03_plan/cert/formal_codegen_semantics_plan.md §(b) — the
  instruction-selection lowering step, the sibling of the MIR→MIR optimization
  proved in `mir_opt_tv`. Same translation-validation (TV) strategy: model a
  per-compile checker `validate : Mir → List MInstr → Bool` that the compiler
  would run after lowering, and prove that ANY lowering it accepts computes the
  same result as the source. We then define the actual lowering `lower` and prove
  it always produces validator-accepted output, so soundness is non-vacuous.

  MODELLED (in scope):
    * SOURCE: a straight-line MIR fragment (`List Instr`) over virtual registers
      (Nat); values are FAITHFUL 64-bit machine words (`BitVec 64`). `+` wraps
      modulo 2^64, exactly like the backend's 64-bit `add`. Instructions:
      `const dst v`, `add dst a b`, `copy dst src`.
    * TARGET: a small machine ISA `MInstr` with its OWN machine-state semantics:
        - `MLoadImm rd imm`  — load a literal into a machine register,
        - `MAdd rd rs rt`     — `rd := rs + rt` (same wrapping `BitVec 64` add),
        - `MMove rd rs`       — register-to-register move,
        - `MSub rd rs rt`     — `rd := rs - rt` (present in the ISA so the
                                 adversary can MIS-SELECT `add`→`sub`; never
                                 produced by the correct lowering).
    * A machine-state semantics `evalMachine : List MInstr → MEnv → MEnv`, wholly
      separate from the source semantics `evalMir`.
    * An encoding `encode : Env → MEnv` of the source register file into the
      machine register file (here the identity register map — the machine reuses
      the source's virtual-register indices; a non-trivial register ASSIGNMENT is
      the separate register-allocation pass, out of scope, see below).
    * The lowering `lower : MIR instr → List MInstr` (one machine instruction per
      source instruction here) and the validator `validate`.

  OUT OF SCOPE (deferred per plan §(b), NOT assumed sound here): register
  ALLOCATION / a non-identity register assignment, multi-ISA / real target
  backends (x86-64, ARM64, RISC-V encodings), machine instructions beyond the
  four modelled (loads/stores/branches/calls/flags/addressing modes),
  signedness/width other than 64-bit wrapping add, and the interpreter path.

  All theorems use the Lean core library only (no Mathlib) and NO proof-trust
  bypasses — the repo's `check-lean-proofs.shs` TRUST_RE gate must find nothing.
  Adversarial disproofs use kernel `decide` (NOT `native_decide`, which would add
  the `ofReduceBool` axiom).
-/
namespace MirIselTv

/-! ## 1. Source MIR syntax and semantics -/

/-- A (virtual / machine) register is identified by a natural number. -/
abbrev Reg : Type := Nat

/-- Machine values are 64-bit words. `+`/`-` on `BitVec 64` wrap modulo 2^64,
    faithfully modelling the backend's overflow behaviour. -/
abbrev Val : Type := BitVec 64

/-- Straight-line source MIR instructions. -/
inductive Instr where
  /-- `const dst v` : write literal `v` into register `dst`. -/
  | const : Reg → Val → Instr
  /-- `add dst a b` : `dst := a + b`. -/
  | add   : Reg → Reg → Reg → Instr
  /-- `copy dst src` : `dst := src`. -/
  | copy  : Reg → Reg → Instr
  deriving DecidableEq

/-- A source MIR fragment is a straight-line list of instructions. -/
abbrev Mir : Type := List Instr

/-- A register file maps every register to its current value. -/
abbrev Env : Type := Reg → Val

/-- Point update of a register file. -/
def upd (env : Env) (r : Reg) (v : Val) : Env :=
  fun x => if x = r then v else env x

/-- One-step source execution. -/
def evalInstr (env : Env) (i : Instr) : Env :=
  match i with
  | .const d v => upd env d v
  | .add d a b => upd env d (env a + env b)
  | .copy d s  => upd env d (env s)

/-- Whole source-fragment semantics. -/
def evalMir (p : Mir) (env : Env) : Env :=
  p.foldl evalInstr env

/-! ## 2. Target machine ISA and its own machine-state semantics -/

/-- The target machine register file is the same shape as the source's; the
    encoding below maps between them. -/
abbrev MEnv : Type := Reg → Val

/-- The small target ISA. `MSub` is a genuine machine instruction (real ISAs have
    subtract) that the CORRECT lowering never emits — its presence lets us state
    the adversarial "select `add` as `sub`" mis-lowering. -/
inductive MInstr where
  /-- `MLoadImm rd imm` : `rd := imm`. -/
  | MLoadImm : Reg → Val → MInstr
  /-- `MAdd rd rs rt` : `rd := rs + rt`. -/
  | MAdd     : Reg → Reg → Reg → MInstr
  /-- `MMove rd rs` : `rd := rs`. -/
  | MMove    : Reg → Reg → MInstr
  /-- `MSub rd rs rt` : `rd := rs - rt`. -/
  | MSub     : Reg → Reg → Reg → MInstr
  deriving DecidableEq

/-- One-step machine execution over the machine register file. This is a wholly
    separate semantics from `evalInstr`, sharing only the `upd` primitive and the
    faithful `BitVec 64` arithmetic. -/
def evalMInstr (env : MEnv) (m : MInstr) : MEnv :=
  match m with
  | .MLoadImm d v => upd env d v
  | .MAdd d a b   => upd env d (env a + env b)
  | .MMove d s    => upd env d (env s)
  | .MSub d a b   => upd env d (env a - env b)

/-- Whole machine-program semantics: fold the per-instruction step left-to-right. -/
def evalMachine (p : List MInstr) (env : MEnv) : MEnv :=
  p.foldl evalMInstr env

/-- Encode a source register file as a machine register file. Here the register
    map is the IDENTITY (the machine reuses the source's register indices); a
    non-identity register ASSIGNMENT is register allocation, out of scope. -/
def encode (env : Env) : MEnv := env

/-! ## 3. The lowering (instruction selection) -/

/-- Lower one source instruction to a machine-instruction sequence. Each source
    instruction selects exactly ONE machine instruction here. -/
def lowerInstr (i : Instr) : List MInstr :=
  match i with
  | .const d v => [MInstr.MLoadImm d v]
  | .add d a b => [MInstr.MAdd d a b]
  | .copy d s  => [MInstr.MMove d s]

/-- Lower a whole fragment by concatenating the per-instruction lowerings. -/
def lower (p : Mir) : List MInstr := p.flatMap lowerInstr

/-! ## 4. Per-instruction correspondence -/

/-- Running the machine code for a SINGLE source instruction reproduces the
    source step exactly. Each equation is between the SAME `upd …` term on both
    sides, so this needs no funext and no axioms. -/
theorem lowerInstr_correct (env : Env) (i : Instr) :
    evalMachine (lowerInstr i) (encode env) = encode (evalInstr env i) := by
  cases i <;> rfl

/-! ## 5. End-to-end lowering soundness (the total lowering is correct) -/

/-- **Lowering preserves the whole register file.** For every fragment and input,
    executing the lowered machine program from the encoded state yields the
    encoding of the source's final register file. Proved by induction over the
    fragment; overflow is preserved because both `add`s are the same wrapping
    `BitVec 64` `+`. -/
theorem lower_sound_env (prog : Mir) (env : Env) :
    evalMachine (lower prog) (encode env) = encode (evalMir prog env) := by
  induction prog generalizing env with
  | nil => rfl
  | cons i is ih =>
    show evalMachine ((i :: is).flatMap lowerInstr) (encode env)
         = encode (evalMir (i :: is) env)
    rw [List.flatMap_cons]
    unfold evalMachine
    rw [List.foldl_append]
    -- Reduce the head machine segment to one source step, then recurse.
    have hhead : (lowerInstr i).foldl evalMInstr (encode env)
                   = encode (evalInstr env i) := lowerInstr_correct env i
    rw [hhead]
    show evalMachine (is.flatMap lowerInstr) (encode (evalInstr env i))
         = encode (evalMir (i :: is) env)
    rw [show evalMir (i :: is) env = evalMir is (evalInstr env i) from rfl]
    exact ih (evalInstr env i)

/-- **Main instruction-selection soundness, observed at a result register.**
    Exactly the plan's statement: for every program, input, and observed result
    register `r`, the machine value equals the source value. Follows from the
    whole-register-file lemma by observing at `r`. -/
theorem lower_sound (prog : Mir) (env : Env) (r : Reg) :
    evalMachine (lower prog) (encode env) r = evalMir prog env r :=
  congrFun (lower_sound_env prog env) r

/-! ## 6. The translation validator (meaningful, per-instruction well-formedness)

    `validate src tgt` checks lockstep that each source instruction was lowered to
    a machine instruction that IMPLEMENTS it (matching opcode and operands). It is
    NOT trivially true: an opcode mis-selection (`add`→`MSub`), a wrong operand,
    or a length mismatch makes it fail (see the adversarial section). -/

/-- Is machine instruction `m` a correct selection of source instruction `i`? -/
def checkLower (i : Instr) (m : MInstr) : Bool :=
  match i, m with
  | .const d v, .MLoadImm d' v' => decide (d = d') && decide (v = v')
  | .add d a b, .MAdd d' a' b'  => decide (d = d') && decide (a = a') && decide (b = b')
  | .copy d s,  .MMove d' s'    => decide (d = d') && decide (s = s')
  | _, _ => false

/-- Lockstep validation: source and machine programs must have equal length and
    each pair must satisfy `checkLower`. (One machine instruction per source
    instruction, matching the singleton lowering.) -/
def validate : Mir → List MInstr → Bool
  | [],      []      => true
  | i :: is, m :: ms => checkLower i m && validate is ms
  | _,       _       => false

/-! ## 7. Validator soundness -/

/-- An accepted per-instruction selection computes the same step as the source.
    Each accepting branch forces `m` to be the opcode/operands that make
    `evalMInstr env m` definitionally the `upd …` of `evalInstr env i`. -/
theorem checkLower_sound (env : MEnv) (i : Instr) (m : MInstr)
    (h : checkLower i m = true) : evalMInstr env m = evalInstr env i := by
  cases i with
  | const d v =>
    cases m with
    | MLoadImm d' v' =>
      simp only [checkLower, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hd, hv⟩ := h; subst hd; subst hv; rfl
    | MAdd d' a' b' => simp [checkLower] at h
    | MMove d' s' => simp [checkLower] at h
    | MSub d' a' b' => simp [checkLower] at h
  | add d a b =>
    cases m with
    | MAdd d' a' b' =>
      simp only [checkLower, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hd, ha⟩, hb⟩ := h; subst hd; subst ha; subst hb; rfl
    | MLoadImm d' v' => simp [checkLower] at h
    | MMove d' s' => simp [checkLower] at h
    | MSub d' a' b' => simp [checkLower] at h
  | copy d s =>
    cases m with
    | MMove d' s' =>
      simp only [checkLower, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hd, hs⟩ := h; subst hd; subst hs; rfl
    | MLoadImm d' v' => simp [checkLower] at h
    | MAdd d' a' b' => simp [checkLower] at h
    | MSub d' a' b' => simp [checkLower] at h

/-- **Validator soundness.** If `validate` accepts a machine program as a lowering
    of the source, the machine program computes the same final register file on
    every input — hence the same value at every observed result register. -/
theorem validate_sound (src : Mir) (tgt : List MInstr) (h : validate src tgt = true) :
    ∀ env, evalMachine tgt (encode env) = encode (evalMir src env) := by
  induction src generalizing tgt with
  | nil =>
    cases tgt with
    | nil => intro env; rfl
    | cons t ts => simp [validate] at h
  | cons i is ih =>
    cases tgt with
    | nil => simp [validate] at h
    | cons t ts =>
      simp only [validate, Bool.and_eq_true] at h
      obtain ⟨hc, hrest⟩ := h
      intro env
      unfold evalMachine evalMir
      simp only [List.foldl_cons]
      have hstep : evalMInstr (encode env) t = evalInstr env i :=
        checkLower_sound (encode env) i t hc
      rw [hstep]
      -- `encode` is the identity, so `encode (evalInstr env i) = evalInstr env i`.
      exact ih ts hrest (evalInstr env i)

/-! ## 8. Non-vacuity: the real lowering always validates -/

/-- The validator accepts everything the lowering produces. -/
theorem validate_lower (p : Mir) : validate p (lower p) = true := by
  induction p with
  | nil => rfl
  | cons i is ih =>
    -- `lower (i :: is)` reduces to `(single machine instr) :: lower is`.
    have hl : lower (i :: is) = lowerInstr i ++ lower is := by
      simp [lower, List.flatMap_cons]
    rw [hl]
    cases i with
    | const d v => simp [lowerInstr, validate, checkLower, ih]
    | add d a b => simp [lowerInstr, validate, checkLower, ih]
    | copy d s  => simp [lowerInstr, validate, checkLower, ih]

/-- **Non-vacuity corollary.** `validate_sound` is not vacuous: the actual
    lowering is a validator-accepted lowering, and combining the two theorems
    reproves end-to-end soundness through the checker. -/
theorem lower_validated_sound (prog : Mir) (env : Env) :
    evalMachine (lower prog) (encode env) = encode (evalMir prog env) :=
  validate_sound prog (lower prog) (validate_lower prog) env

/-! ## 9. Overflow-faithfulness (the honesty payload)

    Because `Val = BitVec 64` and `+` wraps, the lowered `MAdd` computes the SAME
    wrapping result as the source `add` even on overflow — an unbounded-`Int`
    model would certify a fold the hardware does not perform. -/

/-- The largest unsigned 64-bit word, `2^64 - 1`. -/
def maxU64 : Val := 0xFFFFFFFFFFFFFFFF

/-- Overflow is real: `maxU64 + 1` wraps to `0`. -/
theorem wrap_overflow : maxU64 + 1 = 0 := by decide

/-- An overflowing source `add`, and its lowering, agree at the result register:
    both wrap to `0`. -/
def ovSrc : Mir := [Instr.const 0 maxU64, Instr.const 1 1, Instr.add 2 0 1]

theorem ov_lower_matches :
    evalMachine (lower ovSrc) (encode (fun _ => 0)) 2
      = evalMir ovSrc (fun _ => 0) 2 := by decide

theorem ov_result_wraps : evalMir ovSrc (fun _ => 0) 2 = 0 := by decide

/-! ## 10. Adversarial mis-selection (plan §(b) acceptance criterion 3)

    A deliberately WRONG lowering that selects `add` as machine `MSub`. We prove
    the validator REJECTS it AND that it genuinely computes a different result —
    so rejection is warranted and the validator is discriminating. -/

/-- Bad lowering: `add` is mis-selected as subtract; other opcodes unchanged. -/
def badLowerInstr (i : Instr) : List MInstr :=
  match i with
  | .const d v => [MInstr.MLoadImm d v]
  | .add d a b => [MInstr.MSub d a b]   -- WRONG: subtract instead of add
  | .copy d s  => [MInstr.MMove d s]

def badLower (p : Mir) : List MInstr := p.flatMap badLowerInstr

/-- Source: r0 := 5; r1 := 3; r2 := r0 + r1   (so r2 = 8). -/
def advSrc : Mir := [Instr.const 0 5, Instr.const 1 3, Instr.add 2 0 1]

/-- The validator rejects the mis-selected (subtract-for-add) lowering. -/
theorem adv_rejected : validate advSrc (badLower advSrc) = false := by decide

/-- …and rejection is warranted: the mis-selection genuinely changes the observed
    result in register 2 (source `5 + 3 = 8` vs machine `5 - 3 = 2`). -/
theorem adv_semantics_differ :
    evalMachine (badLower advSrc) (encode (fun _ => 0)) 2
      ≠ evalMir advSrc (fun _ => 0) 2 := by decide

/-- Sanity: the validator is not "reject everything" — the CORRECT lowering of the
    same source is ACCEPTED, and it computes the matching result. -/
theorem adv_good_accepted : validate advSrc (lower advSrc) = true := by decide

theorem adv_good_matches :
    evalMachine (lower advSrc) (encode (fun _ => 0)) 2
      = evalMir advSrc (fun _ => 0) 2 := by decide

/-- A second adversary: DROP an operand (select `add d a b` as `MMove d a`,
    discarding `b`). Rejected, and result-changing when `b ≠ 0`. -/
def dropLowerInstr (i : Instr) : List MInstr :=
  match i with
  | .const d v => [MInstr.MLoadImm d v]
  | .add d a _b => [MInstr.MMove d a]   -- WRONG: drops operand b
  | .copy d s  => [MInstr.MMove d s]

def dropLower (p : Mir) : List MInstr := p.flatMap dropLowerInstr

theorem drop_rejected : validate advSrc (dropLower advSrc) = false := by decide

theorem drop_semantics_differ :
    evalMachine (dropLower advSrc) (encode (fun _ => 0)) 2
      ≠ evalMir advSrc (fun _ => 0) 2 := by decide

/-! ## 11. Disclosed axiom footprint (must print only Lean-core axioms) -/

#print axioms lower_sound
#print axioms lower_sound_env
#print axioms validate_sound
#print axioms lower_validated_sound
#print axioms wrap_overflow
#print axioms adv_rejected
#print axioms drop_rejected

end MirIselTv
