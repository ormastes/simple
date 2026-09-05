/-
  MirAlgsimpTv — DO-333 translation-validation soundness for an ALGEBRAIC
  SIMPLIFICATION / STRENGTH-REDUCTION MIR→MIR pass.

  Plan: doc/03_plan/cert/formal_codegen_semantics_plan.md §(b) (codegen semantic
  preservation via translation validation).

  This is a SIBLING development to `mir_opt_tv` (constant folding + copy prop) and
  `mir_dce_tv` (dead code). It applies the SAME translation-validation (TV)
  strategy — model a per-compile checker `validate : Mir → Mir → Bool` that the
  compiler runs after the pass, and prove that ANY rewrite it accepts is
  semantics-preserving — but to a DIFFERENT family of rewrites: the algebraic
  identities that a strength-reduction / peephole pass performs.

  IDENTITIES PROVED SOUND (the algebraic-simplification rewrites this validator
  recognizes; each replaces the matched arithmetic instruction with a `copy` or a
  `const`):

      x + 0  ↦  x     (add,  rhs known 0)   → copy
      0 + x  ↦  x     (add,  lhs known 0)   → copy
      x * 1  ↦  x     (mul,  rhs known 1)   → copy
      1 * x  ↦  x     (mul,  lhs known 1)   → copy
      x * 0  ↦  0     (mul,  either op 0)   → const 0
      0 * x  ↦  0     (mul,  either op 0)   → const 0
      x - x  ↦  0     (sub,  same register) → const 0

  MODELLED (in scope):
    * A straight-line MIR fragment: a `List Instr` over virtual registers (Nat).
      Values are FAITHFUL 64-bit machine words (`BitVec 64`); `+`/`*`/`-` on
      `BitVec 64` are native two's-complement operations modulo 2^64 — they WRAP
      on overflow, exactly like the real backend's 64-bit `add`/`mul`/`sub`. This
      is what makes the identities honest: `x - x = 0` and `x * 0 = 0` are
      THEOREMS of two's-complement arithmetic (`BitVec.sub_self`, `BitVec.mul_zero`),
      not artefacts of an idealised unbounded-integer model.
    * Instructions: `const dst v`, `add dst a b`, `copy dst src`, `mul dst a b`,
      `sub dst a b` — the algebraic-simplification-relevant subset.
    * A state-transformer semantics `eval : Mir → Env → Env`.
    * An abstract known-constant environment (needed to justify `x+0`/`x*1`/`x*0`:
      the validator must know an operand really is the literal 0 or 1), the
      simplification pass `opt`, and the validator `validate`.

  OUT OF SCOPE (deferred, NOT assumed sound here): register allocation, instruction
  selection, control flow (branches/loops/calls), memory, signedness/width other
  than 64-bit wrapping arithmetic, distributive/associative multi-instruction
  rewrites, division/remainder strength reduction, and the interpreter path.

  Proved with the Lean core library only (no Mathlib) and no proof-trust bypasses
  — the repo's `check-lean-proofs.shs` TRUST_RE gate must find nothing. The only
  disclosed axioms are `propext`/`Classical.choice`/`Quot.sound` (Lean stdlib), as
  the `#print axioms` at the end confirms.
-/
namespace MirAlgsimpTv

/-! ## 1. Syntax of the MIR fragment -/

/-- A virtual register is identified by a natural number. -/
abbrev Reg : Type := Nat

/-- Machine values are 64-bit words. `+`/`*`/`-` on `BitVec 64` wrap modulo 2^64,
    faithfully modelling the backend's overflow behaviour (see file header). -/
abbrev Val : Type := BitVec 64

/-- Straight-line MIR instructions over the strength-reduction subset. -/
inductive Instr where
  /-- `const dst v` : write the literal `v` into register `dst`. -/
  | const : Reg → Val → Instr
  /-- `add dst a b` : `dst := a + b`. -/
  | add   : Reg → Reg → Reg → Instr
  /-- `copy dst src` : `dst := src`. -/
  | copy  : Reg → Reg → Instr
  /-- `mul dst a b` : `dst := a * b`. -/
  | mul   : Reg → Reg → Reg → Instr
  /-- `sub dst a b` : `dst := a - b`. -/
  | sub   : Reg → Reg → Reg → Instr
  deriving DecidableEq

/-- A MIR fragment is a straight-line list of instructions. -/
abbrev Mir : Type := List Instr

/-! ## 2. Concrete semantics -/

/-- A register file maps every register to its current value. -/
abbrev Env : Type := Reg → Val

/-- Point update of a register file. -/
def upd (env : Env) (r : Reg) (v : Val) : Env :=
  fun x => if x = r then v else env x

@[simp] theorem upd_hit (env : Env) (r : Reg) (v : Val) : upd env r v r = v := by
  unfold upd; simp

/-- One-step concrete execution of a single instruction. -/
def evalInstr (env : Env) (i : Instr) : Env :=
  match i with
  | .const d v => upd env d v
  | .add d a b => upd env d (env a + env b)
  | .copy d s  => upd env d (env s)
  | .mul d a b => upd env d (env a * env b)
  | .sub d a b => upd env d (env a - env b)

/-- Whole-fragment semantics: fold the per-instruction step left-to-right. -/
def eval (p : Mir) (env : Env) : Env :=
  p.foldl evalInstr env

/-! ## 3. Abstract known-constant environment

    The validator needs to know that an operand of `add`/`mul` really holds the
    literal 0 or 1. We track that with an abstract environment: `some c` means
    "this register provably holds constant `c` here"; `none` means "unknown".
    Only `const` populates it; every other instruction conservatively invalidates
    its destination (KNOWS NOTHING), which is a sound over-approximation and keeps
    the transfer function trivial. -/

/-- Abstract environment. -/
abbrev AbsEnv : Type := Reg → Option Val

/-- The empty abstract environment: nothing is known. -/
def absTop : AbsEnv := fun _ => none

/-- Point update of the abstract environment. -/
def absUpd (σ : AbsEnv) (r : Reg) (v : Option Val) : AbsEnv :=
  fun x => if x = r then v else σ x

/-- Abstract transfer function: only `const` records a known constant; every other
    instruction clears its destination. -/
def absStep (σ : AbsEnv) (i : Instr) : AbsEnv :=
  match i with
  | .const d v => absUpd σ d (some v)
  | .add d _ _ => absUpd σ d none
  | .copy d _  => absUpd σ d none
  | .mul d _ _ => absUpd σ d none
  | .sub d _ _ => absUpd σ d none

/-- Soundness of an abstract environment w.r.t. a concrete one: every register the
    abstraction claims is a known constant really holds that value. -/
def absSound (σ : AbsEnv) (env : Env) : Prop :=
  ∀ r v, σ r = some v → env r = v

theorem absTop_sound (env : Env) : absSound absTop env := by
  intro r v h
  simp [absTop] at h

/-- Clearing a destination to `none` keeps soundness, whatever value is written. -/
theorem absUpd_none_sound (σ : AbsEnv) (env : Env) (d : Reg) (val : Val)
    (h : absSound σ env) : absSound (absUpd σ d none) (upd env d val) := by
  intro r v hr
  by_cases hd : r = d
  · subst hd; simp [absUpd] at hr
  · simp only [absUpd, upd, hd, if_neg hd] at hr ⊢; exact h r v hr

/-- The abstract transfer function preserves soundness across a concrete step. -/
theorem absStep_sound (σ : AbsEnv) (env : Env) (i : Instr)
    (h : absSound σ env) : absSound (absStep σ i) (evalInstr env i) := by
  cases i with
  | const d c =>
    intro r v hr
    simp only [absStep, absUpd, evalInstr, upd] at hr ⊢
    by_cases hd : r = d
    · subst hd; simp at hr ⊢; exact hr
    · simp [hd] at hr ⊢; exact h r v hr
  | add d a b => exact absUpd_none_sound σ env d (env a + env b) h
  | copy d s  => exact absUpd_none_sound σ env d (env s) h
  | mul d a b => exact absUpd_none_sound σ env d (env a * env b) h
  | sub d a b => exact absUpd_none_sound σ env d (env a - env b) h

/-! ## 4. The translation validator

    Per-instruction check `checkInstr σ s t`: is rewriting source instruction `s`
    into target instruction `t` justified under the known constants `σ`?

    Accept iff EITHER `t` is syntactically identical to `s` (no rewrite), OR one of
    the seven algebraic identities holds:
      * `add d a b ↦ copy d src` when `σ` proves the OTHER operand is 0,
      * `mul d a b ↦ copy d src` when `σ` proves the OTHER operand is 1,
      * `mul d a b ↦ const d 0`  when `σ` proves EITHER operand is 0,
      * `sub d a b ↦ const d 0`  when `a` and `b` are the SAME register. -/
def checkInstr (σ : AbsEnv) (s t : Instr) : Bool :=
  match s, t with
  | .add d a b, .copy d' src =>
      decide (d = d') &&
        ((decide (σ b = some 0) && decide (src = a)) ||
         (decide (σ a = some 0) && decide (src = b)))
  | .mul d a b, .copy d' src =>
      decide (d = d') &&
        ((decide (σ b = some 1) && decide (src = a)) ||
         (decide (σ a = some 1) && decide (src = b)))
  | .mul d a b, .const d' v =>
      decide (d = d') && decide (v = 0) &&
        (decide (σ a = some 0) || decide (σ b = some 0))
  | .sub d a b, .const d' v =>
      decide (d = d') && decide (v = 0) && decide (a = b)
  | _, _ => decide (s = t)

/-- Lockstep validation of two fragments, threading the abstract environment
    (advanced by the SOURCE instructions). -/
def validateAux (σ : AbsEnv) : Mir → Mir → Bool
  | [],      []      => true
  | s :: ss, t :: ts => checkInstr σ s t && validateAux (absStep σ s) ss ts
  | _,       _       => false

/-- The translation validator: run lockstep validation from the empty abstract
    environment. -/
def validate (src tgt : Mir) : Bool := validateAux absTop src tgt

/-! ## 5. Soundness: every accepted per-instruction rewrite preserves the step -/

theorem checkInstr_sound (σ : AbsEnv) (s t : Instr) (env : Env)
    (hσ : absSound σ env) (hc : checkInstr σ s t = true) :
    evalInstr env s = evalInstr env t := by
  cases s with
  | const d v =>
    have heq : Instr.const d v = t := by
      simp only [checkInstr, decide_eq_true_eq] at hc; exact hc
    rw [heq]
  | copy d s =>
    have heq : Instr.copy d s = t := by
      simp only [checkInstr, decide_eq_true_eq] at hc; exact hc
    rw [heq]
  | add d a b =>
    cases t with
    | copy d' src =>
      simp only [checkInstr, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hd, hor⟩ := hc; subst hd
      simp only [evalInstr]
      rcases hor with ⟨hb, hsa⟩ | ⟨ha, hsb⟩
      · rw [hsa]
        have hv : env a + env b = env a := by rw [hσ b 0 hb]; exact BitVec.add_zero (env a)
        rw [hv]
      · rw [hsb]
        have hv : env a + env b = env b := by rw [hσ a 0 ha]; exact BitVec.zero_add (env b)
        rw [hv]
    | const d' v =>
      have heq : Instr.add d a b = Instr.const d' v := by
        simp only [checkInstr, decide_eq_true_eq] at hc; exact hc
      rw [heq]
    | add d' a' b' =>
      have heq : Instr.add d a b = Instr.add d' a' b' := by
        simp only [checkInstr, decide_eq_true_eq] at hc; exact hc
      rw [heq]
    | mul d' a' b' =>
      have heq : Instr.add d a b = Instr.mul d' a' b' := by
        simp only [checkInstr, decide_eq_true_eq] at hc; exact hc
      rw [heq]
    | sub d' a' b' =>
      have heq : Instr.add d a b = Instr.sub d' a' b' := by
        simp only [checkInstr, decide_eq_true_eq] at hc; exact hc
      rw [heq]
  | mul d a b =>
    cases t with
    | copy d' src =>
      simp only [checkInstr, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hd, hor⟩ := hc; subst hd
      simp only [evalInstr]
      rcases hor with ⟨hb, hsa⟩ | ⟨ha, hsb⟩
      · rw [hsa]
        have hv : env a * env b = env a := by rw [hσ b 1 hb]; exact BitVec.mul_one (env a)
        rw [hv]
      · rw [hsb]
        have hv : env a * env b = env b := by rw [hσ a 1 ha]; exact BitVec.one_mul (env b)
        rw [hv]
    | const d' v =>
      simp only [checkInstr, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨hd, hzero⟩, hor⟩ := hc; subst hd; subst hzero
      simp only [evalInstr]
      rcases hor with ha | hb
      · have hv : env a * env b = (0 : Val) := by rw [hσ a 0 ha]; exact BitVec.zero_mul
        rw [hv]
      · have hv : env a * env b = (0 : Val) := by rw [hσ b 0 hb]; exact BitVec.mul_zero
        rw [hv]
    | add d' a' b' =>
      have heq : Instr.mul d a b = Instr.add d' a' b' := by
        simp only [checkInstr, decide_eq_true_eq] at hc; exact hc
      rw [heq]
    | mul d' a' b' =>
      have heq : Instr.mul d a b = Instr.mul d' a' b' := by
        simp only [checkInstr, decide_eq_true_eq] at hc; exact hc
      rw [heq]
    | sub d' a' b' =>
      have heq : Instr.mul d a b = Instr.sub d' a' b' := by
        simp only [checkInstr, decide_eq_true_eq] at hc; exact hc
      rw [heq]
  | sub d a b =>
    cases t with
    | const d' v =>
      simp only [checkInstr, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨hd, hzero⟩, hab⟩ := hc; subst hd; subst hzero
      simp only [evalInstr]
      have hv : env a - env b = (0 : Val) := by rw [hab]; exact BitVec.sub_self (env b)
      rw [hv]
    | copy d' src =>
      have heq : Instr.sub d a b = Instr.copy d' src := by
        simp only [checkInstr, decide_eq_true_eq] at hc; exact hc
      rw [heq]
    | add d' a' b' =>
      have heq : Instr.sub d a b = Instr.add d' a' b' := by
        simp only [checkInstr, decide_eq_true_eq] at hc; exact hc
      rw [heq]
    | mul d' a' b' =>
      have heq : Instr.sub d a b = Instr.mul d' a' b' := by
        simp only [checkInstr, decide_eq_true_eq] at hc; exact hc
      rw [heq]
    | sub d' a' b' =>
      have heq : Instr.sub d a b = Instr.sub d' a' b' := by
        simp only [checkInstr, decide_eq_true_eq] at hc; exact hc
      rw [heq]

/-- Core soundness over lists. -/
theorem validateAux_sound (σ : AbsEnv) (src tgt : Mir) (env : Env)
    (hσ : absSound σ env) (h : validateAux σ src tgt = true) :
    src.foldl evalInstr env = tgt.foldl evalInstr env := by
  induction src generalizing σ tgt env with
  | nil =>
    cases tgt with
    | nil => rfl
    | cons t ts => simp [validateAux] at h
  | cons s ss ih =>
    cases tgt with
    | nil => simp [validateAux] at h
    | cons t ts =>
      unfold validateAux at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨hstep, hrest⟩ := h
      have hstepEq : evalInstr env s = evalInstr env t :=
        checkInstr_sound σ s t env hσ hstep
      have hσ' : absSound (absStep σ s) (evalInstr env s) :=
        absStep_sound σ env s hσ
      simp only [List.foldl_cons]
      rw [← hstepEq]
      exact ih (absStep σ s) ts (evalInstr env s) hσ' hrest

/-- **Main TV soundness theorem.** Any rewrite the validator accepts preserves the
    whole-fragment semantics on every input register file. -/
theorem validate_sound (src tgt : Mir) (h : validate src tgt = true) :
    ∀ env, eval src env = eval tgt env := by
  intro env
  unfold eval
  exact validateAux_sound absTop src tgt env (absTop_sound env) h

/-! ## 6. The simplification pass, and its non-vacuity -/

/-- Simplify one instruction under the known-constant environment `σ`, applying
    the first algebraic identity that fires; otherwise leave it unchanged. -/
def optInstr (σ : AbsEnv) (i : Instr) : Instr :=
  match i with
  | .add d a b =>
      if σ a = some 0 then .copy d b
      else if σ b = some 0 then .copy d a
      else i
  | .mul d a b =>
      if σ a = some 0 then .const d 0
      else if σ b = some 0 then .const d 0
      else if σ a = some 1 then .copy d b
      else if σ b = some 1 then .copy d a
      else i
  | .sub d a b => if a = b then .const d 0 else i
  | .const _ _ => i
  | .copy _ _  => i

/-- Simplify a whole fragment, threading the abstract environment. -/
def optAux (σ : AbsEnv) : Mir → Mir
  | []      => []
  | i :: is => optInstr σ i :: optAux (absStep σ i) is

/-- Algebraic-simplification pass over a straight-line fragment. -/
def opt (p : Mir) : Mir := optAux absTop p

/-- The validator accepts every instruction the simplifier produces. -/
theorem checkInstr_optInstr (σ : AbsEnv) (i : Instr) :
    checkInstr σ i (optInstr σ i) = true := by
  cases i with
  | const d v => simp [optInstr, checkInstr]
  | copy d s => simp [optInstr, checkInstr]
  | add d a b =>
    by_cases ha : σ a = some 0
    · have hopt : optInstr σ (Instr.add d a b) = Instr.copy d b := by
        simp only [optInstr, if_pos ha]
      rw [hopt]; simp [checkInstr, ha]
    · by_cases hb : σ b = some 0
      · have hopt : optInstr σ (Instr.add d a b) = Instr.copy d a := by
          simp only [optInstr, if_neg ha, if_pos hb]
        rw [hopt]; simp [checkInstr, hb]
      · have hopt : optInstr σ (Instr.add d a b) = Instr.add d a b := by
          simp only [optInstr, if_neg ha, if_neg hb]
        rw [hopt]; simp [checkInstr]
  | mul d a b =>
    by_cases ha : σ a = some 0
    · have hopt : optInstr σ (Instr.mul d a b) = Instr.const d 0 := by
        simp only [optInstr, if_pos ha]
      rw [hopt]; simp [checkInstr, ha]
    · by_cases hb : σ b = some 0
      · have hopt : optInstr σ (Instr.mul d a b) = Instr.const d 0 := by
          simp only [optInstr, if_neg ha, if_pos hb]
        rw [hopt]; simp [checkInstr, hb]
      · by_cases ha1 : σ a = some 1
        · have hopt : optInstr σ (Instr.mul d a b) = Instr.copy d b := by
            simp only [optInstr, if_neg ha, if_neg hb, if_pos ha1]
          rw [hopt]; simp [checkInstr, ha1]
        · by_cases hb1 : σ b = some 1
          · have hopt : optInstr σ (Instr.mul d a b) = Instr.copy d a := by
              simp only [optInstr, if_neg ha, if_neg hb, if_neg ha1, if_pos hb1]
            rw [hopt]; simp [checkInstr, hb1]
          · have hopt : optInstr σ (Instr.mul d a b) = Instr.mul d a b := by
              simp only [optInstr, if_neg ha, if_neg hb, if_neg ha1, if_neg hb1]
            rw [hopt]; simp [checkInstr]
  | sub d a b =>
    by_cases hab : a = b
    · have hopt : optInstr σ (Instr.sub d a b) = Instr.const d 0 := by
        simp only [optInstr, if_pos hab]
      rw [hopt]; simp [checkInstr, hab]
    · have hopt : optInstr σ (Instr.sub d a b) = Instr.sub d a b := by
        simp only [optInstr, if_neg hab]
      rw [hopt]; simp [checkInstr]

/-- Lockstep: the validator accepts the whole simplified fragment. -/
theorem validateAux_optAux (σ : AbsEnv) (p : Mir) :
    validateAux σ p (optAux σ p) = true := by
  induction p generalizing σ with
  | nil => rfl
  | cons i is ih =>
    unfold optAux validateAux
    rw [checkInstr_optInstr σ i]
    simp only [Bool.true_and]
    exact ih (absStep σ i)

/-- **Non-vacuity.** The simplifier's output always passes the validator. -/
theorem opt_validates (p : Mir) : validate p (opt p) = true :=
  validateAux_optAux absTop p

/-- **Corollary: the simplification pass is semantics-preserving.** -/
theorem opt_sound (p : Mir) : ∀ env, eval p env = eval (opt p) env :=
  validate_sound p (opt p) (opt_validates p)

/-! ## 7. Per-identity non-vacuity

    Each of the seven identities gets a concrete `(src, tgt)` witness. For each we
    prove: the validator ACCEPTS it (so `validate_sound` is non-vacuous for that
    identity), it is a GENUINE rewrite (`src ≠ tgt`), and — piping the acceptance
    proof through the main theorem — the rewrite PRESERVES semantics on every
    input. Register 0 is an unknown input; a preceding `const` supplies the 0/1
    the identity needs. -/

-- x + 0 = x
def id1Src : Mir := [Instr.const 1 0, Instr.add 2 0 1]
def id1Tgt : Mir := [Instr.const 1 0, Instr.copy 2 0]
theorem id1_validates : validate id1Src id1Tgt = true := by decide
theorem id1_real : id1Src ≠ id1Tgt := by decide
theorem id1_sound : ∀ env, eval id1Src env = eval id1Tgt env :=
  validate_sound id1Src id1Tgt id1_validates

-- 0 + x = x
def id2Src : Mir := [Instr.const 1 0, Instr.add 2 1 0]
def id2Tgt : Mir := [Instr.const 1 0, Instr.copy 2 0]
theorem id2_validates : validate id2Src id2Tgt = true := by decide
theorem id2_real : id2Src ≠ id2Tgt := by decide
theorem id2_sound : ∀ env, eval id2Src env = eval id2Tgt env :=
  validate_sound id2Src id2Tgt id2_validates

-- x * 1 = x
def id3Src : Mir := [Instr.const 1 1, Instr.mul 2 0 1]
def id3Tgt : Mir := [Instr.const 1 1, Instr.copy 2 0]
theorem id3_validates : validate id3Src id3Tgt = true := by decide
theorem id3_real : id3Src ≠ id3Tgt := by decide
theorem id3_sound : ∀ env, eval id3Src env = eval id3Tgt env :=
  validate_sound id3Src id3Tgt id3_validates

-- 1 * x = x
def id4Src : Mir := [Instr.const 1 1, Instr.mul 2 1 0]
def id4Tgt : Mir := [Instr.const 1 1, Instr.copy 2 0]
theorem id4_validates : validate id4Src id4Tgt = true := by decide
theorem id4_real : id4Src ≠ id4Tgt := by decide
theorem id4_sound : ∀ env, eval id4Src env = eval id4Tgt env :=
  validate_sound id4Src id4Tgt id4_validates

-- x * 0 = 0
def id5Src : Mir := [Instr.const 1 0, Instr.mul 2 0 1]
def id5Tgt : Mir := [Instr.const 1 0, Instr.const 2 0]
theorem id5_validates : validate id5Src id5Tgt = true := by decide
theorem id5_real : id5Src ≠ id5Tgt := by decide
theorem id5_sound : ∀ env, eval id5Src env = eval id5Tgt env :=
  validate_sound id5Src id5Tgt id5_validates

-- 0 * x = 0
def id6Src : Mir := [Instr.const 1 0, Instr.mul 2 1 0]
def id6Tgt : Mir := [Instr.const 1 0, Instr.const 2 0]
theorem id6_validates : validate id6Src id6Tgt = true := by decide
theorem id6_real : id6Src ≠ id6Tgt := by decide
theorem id6_sound : ∀ env, eval id6Src env = eval id6Tgt env :=
  validate_sound id6Src id6Tgt id6_validates

-- x - x = 0  (purely syntactic: same register, no constant needed)
def id7Src : Mir := [Instr.sub 2 0 0]
def id7Tgt : Mir := [Instr.const 2 0]
theorem id7_validates : validate id7Src id7Tgt = true := by decide
theorem id7_real : id7Src ≠ id7Tgt := by decide
theorem id7_sound : ∀ env, eval id7Src env = eval id7Tgt env :=
  validate_sound id7Src id7Tgt id7_validates

/-- End-to-end: run on the `x - x` source, the pass produces exactly `const 2 0`. -/
theorem opt_id7 : opt id7Src = id7Tgt := by decide

/-! ## 8. Adversarial counter-example (a BOGUS identity is rejected)

    Strength reduction `x * 2 ↦ x` is UNSOUND (it is `x << 1`, not `x`). We prove
    the validator REJECTS it and that the two fragments genuinely disagree —
    demonstrating the validator is discriminating, not accept-everything. Here the
    second operand is the known constant `2` (not `1`), so the `mul ↦ copy` check
    (`σ b = some 1`) fails. -/

/-- Source: r1 := 2; r2 := r0 * r1   (so r2 = r0 * 2). -/
def advSrc : Mir := [Instr.const 1 2, Instr.mul 2 0 1]

/-- Bogus target: claim `x * 2 = x`, i.e. r2 := r0. -/
def advBadTgt : Mir := [Instr.const 1 2, Instr.copy 2 0]

/-- The validator rejects the bogus `x * 2 ↦ x` rewrite. -/
theorem adv_rejected : validate advSrc advBadTgt = false := by decide

/-- …and rejection is warranted: on input r0 = 1 the source gives r2 = 1*2 = 2 but
    the bogus target gives r2 = 1. -/
theorem adv_semantics_differ :
    eval advSrc (fun _ => 1) 2 ≠ eval advBadTgt (fun _ => 1) 2 := by decide

/-- The pass itself does NOT fire on `x * 2` (2 is neither 0 nor 1): it leaves the
    multiply intact — end-to-end evidence the simplifier only performs the sound
    identities. -/
theorem opt_advSrc_noop : opt advSrc = advSrc := by decide

/-! ## 9. Disclosed axiom footprint -/

#print axioms validate_sound
#print axioms opt_sound
#print axioms id7_sound
#print axioms adv_rejected
#print axioms adv_semantics_differ

end MirAlgsimpTv
