/-
  MirLoopTv — DO-333 translation-validation soundness for a MIR→MIR optimization
  applied INSIDE a bounded LOOP.

  This project extends the straight-line / structured-`ite` translation-validation
  soundness of `mir_opt_tv` to a language WITH LOOPS. Following the same
  translation-validation (TV) strategy — a per-compile checker
  `validate : Program → Program → Bool` that the compiler runs after every
  optimization, proved to accept only semantics-preserving rewrites — we model:

    * straight-line basic blocks (`const`/`add`/`copy` over `BitVec 64`), value
      model FAITHFUL to a 64-bit backend (`+` wraps modulo 2^64), copied verbatim
      from `mir_opt_tv` so the overflow-honesty argument still holds, PLUS
    * a structured `Program` with `block`, `seq`, and a bounded
      `While (condReg, body)` loop.

  TOTALITY VIA FUEL.  A real `loop` need not terminate, so we cannot give it an
  unbounded fixed-point semantics in a total logic.  Instead the evaluator takes a
  `Fuel : Nat` budget: every construct consumes one unit of fuel per step, and
  when fuel runs out evaluation STOPS (returns the current register file).  This
  makes `evalP` STRUCTURALLY recursive on the fuel argument — hence total AND
  kernel-computable, so the adversarial disproofs below discharge by kernel
  `decide` (never `native_decide`, which would add the `ofReduceBool` axiom).

  THE OPTIMIZATION.  We apply the intra-block constant-fold / copy-propagation of
  `mir_opt_tv` to the straight-line blocks, INCLUDING the blocks that make up a
  loop body.  The key soundness subtlety a loop introduces is that constants
  established BEFORE the loop need not survive across iterations; we handle this
  conservatively — the analysis RESETS to "know nothing" (`absTop`) on entry to a
  loop body (and, in this fragment, across every `seq`/`loop` boundary).  This is
  a sound over-approximation (it only ever makes the validator accept FEWER
  rewrites), and it is exactly what lets folding INSIDE the loop body remain valid
  on every iteration, because `absTop` is sound for any register file.

  MAIN THEOREM (`validate_sound`, by induction on fuel):
      validate src tgt = true → ∀ fuel env, evalResult src fuel env
                                            = evalResult tgt fuel env
  where `evalResult` observes the whole final register file (strictly stronger
  than observing one designated result register).

  NON-VACUITY: the optimizer `optProg` always produces validator-accepted output
  (`opt_validates`), and a concrete example folds an `add` of two constants to a
  literal INSIDE the loop body.  ADVERSARIAL: a body rewrite that changes an
  observable inside the loop is REJECTED by the validator and genuinely differs on
  a concrete fueled run.

  OUT OF SCOPE (honest cuts):
    * Cross-`seq` / cross-loop constant propagation: the analysis is intra-block
      only (resets to `absTop` across every control-flow boundary).  Folding
      still happens WITHIN each block, including loop-body blocks.
    * Loop-invariant / dead-loop elimination, loop unrolling, induction-variable
      reasoning: not modelled.  The loop optimization here is exactly "optimize
      the body blocks".
    * Everything already out of scope in `mir_opt_tv`: register allocation,
      instruction selection, memory/calls, non-64-bit widths, the interpreter.

  ZERO proof-trust bypasses (no unsound escape hatches of any kind).  Lean core
  library only.  The disclosed axiom footprint of `validate_sound` is `propext`.
-/
namespace MirLoopTv

/-! ## 1. Straight-line MIR fragment (value model faithful to a 64-bit backend) -/

/-- A virtual register is identified by a natural number. -/
abbrev Reg : Type := Nat

/-- Machine values are 64-bit words; `+` wraps modulo 2^64, faithfully modelling
    the backend's overflow behaviour. -/
abbrev Val : Type := BitVec 64

/-- Straight-line MIR instructions over the constant-fold / copy-prop subset. -/
inductive Instr where
  | const : Reg → Val → Instr
  | add   : Reg → Reg → Reg → Instr
  | copy  : Reg → Reg → Instr
  deriving DecidableEq

/-- A straight-line MIR fragment. -/
abbrev Mir : Type := List Instr

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

/-! ## 2. Abstract constant environment (what the checker/optimizer tracks) -/

/-- `some c` = "provably holds constant `c` here"; `none` = "unknown". -/
abbrev AbsEnv : Type := Reg → Option Val

/-- Nothing is known. -/
def absTop : AbsEnv := fun _ => none

/-- Point update of the abstract environment. -/
def absUpd (σ : AbsEnv) (r : Reg) (v : Option Val) : AbsEnv :=
  fun x => if x = r then v else σ x

/-- Abstract transfer function for one instruction. -/
def absStep (σ : AbsEnv) (i : Instr) : AbsEnv :=
  match i with
  | .const d v => absUpd σ d (some v)
  | .add d a b =>
      match σ a, σ b with
      | some va, some vb => absUpd σ d (some (va + vb))
      | _, _             => absUpd σ d none
  | .copy d s  => absUpd σ d (σ s)

/-- Every register the abstraction claims constant really holds that value. -/
def absSound (σ : AbsEnv) (env : Env) : Prop :=
  ∀ r v, σ r = some v → env r = v

theorem absTop_sound (env : Env) : absSound absTop env := by
  intro r v h
  simp [absTop] at h

/-- The abstract transfer function preserves soundness across a concrete step. -/
theorem absStep_sound (σ : AbsEnv) (env : Env) (i : Instr)
    (h : absSound σ env) : absSound (absStep σ i) (evalInstr env i) := by
  intro r v hr
  cases i with
  | const d c =>
    simp only [absStep, absUpd, evalInstr, upd] at hr ⊢
    by_cases hd : r = d
    · subst hd; simp at hr ⊢; exact hr
    · simp [hd] at hr ⊢; exact h r v hr
  | add d a b =>
    simp only [absStep] at hr
    simp only [evalInstr, upd]
    cases ha : σ a with
    | none =>
      simp only [ha, absUpd] at hr
      by_cases hd : r = d
      · subst hd; simp at hr
      · simp [hd] at hr ⊢; exact h r v hr
    | some va =>
      cases hb : σ b with
      | none =>
        simp only [ha, hb, absUpd] at hr
        by_cases hd : r = d
        · subst hd; simp at hr
        · simp [hd] at hr ⊢; exact h r v hr
      | some vb =>
        simp only [ha, hb, absUpd] at hr
        by_cases hd : r = d
        · subst hd
          simp at hr ⊢
          have hva : env a = va := h a va ha
          have hvb : env b = vb := h b vb hb
          rw [hva, hvb]; exact hr
        · simp [hd] at hr ⊢; exact h r v hr
  | copy d s =>
    simp only [absStep, absUpd] at hr
    simp only [evalInstr, upd]
    by_cases hd : r = d
    · subst hd; simp at hr ⊢; exact h s v hr
    · simp [hd] at hr ⊢; exact h r v hr

/-! ## 3. The straight-line (per-block) translation validator -/

/-- Per-instruction check: is rewriting `s` into `t` justified under known
    constants `σ`?  Accept iff `t = s`, or a valid constant-fold of `add`, or a
    valid copy-of-a-known-constant. -/
def checkInstr (σ : AbsEnv) (s t : Instr) : Bool :=
  match s, t with
  | .add d a b, .const d' v =>
      decide (d = d') &&
        (match σ a, σ b with
         | some va, some vb => decide (v = va + vb)
         | _, _             => false)
  | .copy d src, .const d' v =>
      decide (d = d') &&
        (match σ src with
         | some c => decide (v = c)
         | none   => false)
  | _, _ => decide (s = t)

/-- Lockstep validation of two straight-line blocks, threading the abstract
    environment along the SOURCE instructions. -/
def validateAux (σ : AbsEnv) : Mir → Mir → Bool
  | [],      []      => true
  | s :: ss, t :: ts => checkInstr σ s t && validateAux (absStep σ s) ss ts
  | _,       _       => false

/-- Every accepted per-instruction rewrite preserves the one-step semantics. -/
theorem checkInstr_sound (σ : AbsEnv) (s t : Instr) (env : Env)
    (hσ : absSound σ env) (hc : checkInstr σ s t = true) :
    evalInstr env s = evalInstr env t := by
  cases s with
  | const d v =>
    have heq : Instr.const d v = t := by
      have h2 := hc
      simp only [checkInstr, decide_eq_true_eq] at h2
      exact h2
    rw [heq]
  | add d a b =>
    cases t with
    | const d' v =>
      simp only [checkInstr] at hc
      cases ha : σ a with
      | none => rw [ha] at hc; simp at hc
      | some va =>
        cases hb : σ b with
        | none => rw [ha, hb] at hc; simp at hc
        | some vb =>
          rw [ha, hb] at hc
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          obtain ⟨hdd, hvv⟩ := hc
          subst hdd; subst hvv
          simp only [evalInstr]
          have hva : env a = va := hσ a va ha
          have hvb : env b = vb := hσ b vb hb
          rw [hva, hvb]
    | add d' a' b' =>
      have heq : Instr.add d a b = Instr.add d' a' b' := by
        simp only [checkInstr, decide_eq_true_eq] at hc; exact hc
      rw [heq]
    | copy d' s' =>
      have heq : Instr.add d a b = Instr.copy d' s' := by
        simp only [checkInstr, decide_eq_true_eq] at hc; exact hc
      rw [heq]
  | copy d src =>
    cases t with
    | const d' v =>
      simp only [checkInstr] at hc
      cases hsrc : σ src with
      | none => rw [hsrc] at hc; simp at hc
      | some c =>
        rw [hsrc] at hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨hdd, hvv⟩ := hc
        subst hdd
        simp only [evalInstr]
        have hc' : env src = c := hσ src c hsrc
        rw [hc', ← hvv]
    | add d' a' b' =>
      have heq : Instr.copy d src = Instr.add d' a' b' := by
        simp only [checkInstr, decide_eq_true_eq] at hc; exact hc
      rw [heq]
    | copy d' s' =>
      have heq : Instr.copy d src = Instr.copy d' s' := by
        simp only [checkInstr, decide_eq_true_eq] at hc; exact hc
      rw [heq]

/-- Core straight-line soundness: an accepted block rewrite preserves the fold. -/
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

/-! ## 4. The intra-block optimizer, and its non-vacuity -/

/-- Optimize one instruction under known constants `σ`. -/
def optInstr (σ : AbsEnv) (i : Instr) : Instr :=
  match i with
  | .add d a b =>
      match σ a, σ b with
      | some va, some vb => .const d (va + vb)
      | _, _             => i
  | .copy d s =>
      match σ s with
      | some c => .const d c
      | none   => i
  | .const _ _ => i

/-- Optimize a whole block, threading the abstract environment. -/
def optAux (σ : AbsEnv) : Mir → Mir
  | []      => []
  | i :: is => optInstr σ i :: optAux (absStep σ i) is

/-- The validator accepts every instruction the optimizer produces. -/
theorem checkInstr_optInstr (σ : AbsEnv) (i : Instr) :
    checkInstr σ i (optInstr σ i) = true := by
  cases i with
  | const d v => simp [checkInstr, optInstr]
  | add d a b =>
    cases ha : σ a with
    | none =>
      have hopt : optInstr σ (Instr.add d a b) = Instr.add d a b := by
        simp [optInstr, ha]
      rw [hopt]; simp [checkInstr]
    | some va =>
      cases hb : σ b with
      | none =>
        have hopt : optInstr σ (Instr.add d a b) = Instr.add d a b := by
          simp [optInstr, ha, hb]
        rw [hopt]; simp [checkInstr]
      | some vb =>
        have hopt : optInstr σ (Instr.add d a b) = Instr.const d (va + vb) := by
          simp [optInstr, ha, hb]
        rw [hopt]; simp [checkInstr, ha, hb]
  | copy d s =>
    cases hs : σ s with
    | none =>
      have hopt : optInstr σ (Instr.copy d s) = Instr.copy d s := by
        simp [optInstr, hs]
      rw [hopt]; simp [checkInstr]
    | some c =>
      have hopt : optInstr σ (Instr.copy d s) = Instr.const d c := by
        simp [optInstr, hs]
      rw [hopt]; simp [checkInstr, hs]

/-- Lockstep: the validator accepts the whole optimized block. -/
theorem validateAux_optAux (σ : AbsEnv) (p : Mir) :
    validateAux σ p (optAux σ p) = true := by
  induction p generalizing σ with
  | nil => rfl
  | cons i is ih =>
    unfold optAux validateAux
    rw [checkInstr_optInstr σ i]
    simp only [Bool.true_and]
    exact ih (absStep σ i)

/-! ## 5. Structured programs with a bounded loop -/

/-- Structured control-flow program: straight-line blocks, sequencing, and a
    bounded `loop (condReg ≠ 0) body` loop. -/
inductive Program where
  /-- A straight-line basic block. -/
  | block : Mir → Program
  /-- Sequential composition. -/
  | seq   : Program → Program → Program
  /-- `loop (env condReg ≠ 0) body`. -/
  | loop : Reg → Program → Program
  deriving DecidableEq

/-- Fueled, total, kernel-computable semantics.  Fuel is STRUCTURALLY decreasing
    on every recursive call (each construct consumes one unit), so `evalP` is a
    structural recursion on the fuel argument — total without any well-founded
    obligation, and it reduces in the kernel (so `decide` works below).  When
    fuel is exhausted, evaluation stops with the current register file. -/
def evalP : Nat → Program → Env → Env
  | 0,      _,             env => env
  | _+1,    .block b,      env => b.foldl evalInstr env
  | fuel+1, .seq p q,      env => evalP fuel q (evalP fuel p env)
  | fuel+1, .loop c body, env =>
      if env c ≠ 0 then evalP fuel (.loop c body) (evalP fuel body env) else env

/-- Observable result of a fueled run: the whole final register file (strictly
    stronger than observing a single designated result register). -/
def evalResult (p : Program) (fuel : Nat) (env : Env) : Env := evalP fuel p env

/-! ## 6. The control-flow translation validator

    Across every control-flow boundary (into a `seq` tail, into a loop body) the
    abstract state RESETS to `absTop` ("know nothing") — a sound
    over-approximation.  Only the straight-line blocks fold, using their entry
    `σ`; at the program top level, and after every reset, that entry is `absTop`,
    so folding is justified purely by constants computed within the block itself
    (which holds on every loop iteration). -/
def validateP (σ : AbsEnv) : Program → Program → Bool
  | .block b1, tgt =>
      match tgt with
      | .block b2 => validateAux σ b1 b2
      | _         => false
  | .seq p1 q1, tgt =>
      match tgt with
      | .seq p2 q2 => validateP σ p1 p2 && validateP absTop q1 q2
      | _          => false
  | .loop c1 body1, tgt =>
      match tgt with
      | .loop c2 body2 => decide (c1 = c2) && validateP absTop body1 body2
      | _               => false

/-- The control-flow translation validator: validate from the empty abstract
    environment. -/
def validate (src tgt : Program) : Bool := validateP absTop src tgt

/-! ## 7. Control-flow soundness (by induction on fuel) -/

/-- Core soundness: an accepted control-flow rewrite preserves the fueled
    semantics.  Proof is a single induction on fuel — every construct consumes
    fuel, so every recursive appeal is to the fuel induction hypothesis. -/
theorem validateP_sound :
    ∀ (fuel : Nat) (src : Program) (σ : AbsEnv) (tgt : Program) (env : Env),
      absSound σ env → validateP σ src tgt = true →
      evalP fuel src env = evalP fuel tgt env := by
  intro fuel
  induction fuel with
  | zero =>
    -- Out of fuel: every program evaluates to the current register file.
    intro src σ tgt env _ _
    rfl
  | succ fuel ihf =>
    intro src σ tgt env hσ h
    cases src with
    | block b1 =>
      cases tgt with
      | block b2 =>
        simp only [evalP]
        exact validateAux_sound σ b1 b2 env hσ (by simpa only [validateP] using h)
      | seq _ _   => simp [validateP] at h
      | loop _ _ => simp [validateP] at h
    | seq p1 q1 =>
      cases tgt with
      | block _   => simp [validateP] at h
      | loop _ _ => simp [validateP] at h
      | seq p2 q2 =>
        simp only [validateP, Bool.and_eq_true] at h
        obtain ⟨h1, h2⟩ := h
        simp only [evalP]
        have e1 : evalP fuel p1 env = evalP fuel p2 env := ihf p1 σ p2 env hσ h1
        have e2 : evalP fuel q1 (evalP fuel p1 env)
                = evalP fuel q2 (evalP fuel p1 env) :=
          ihf q1 absTop q2 (evalP fuel p1 env) (absTop_sound _) h2
        rw [e2, e1]
    | loop c1 b1 =>
      cases tgt with
      | block _ => simp [validateP] at h
      | seq _ _ => simp [validateP] at h
      | loop c2 b2 =>
        simp only [validateP, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨hc, hb⟩ := h
        subst hc
        simp only [evalP]
        by_cases hcond : env c1 ≠ 0
        · rw [if_pos hcond, if_pos hcond]
          have ebody : evalP fuel b1 env = evalP fuel b2 env :=
            ihf b1 absTop b2 env (absTop_sound _) hb
          have etail : evalP fuel (Program.loop c1 b1) (evalP fuel b1 env)
                     = evalP fuel (Program.loop c1 b2) (evalP fuel b1 env) := by
            apply ihf (Program.loop c1 b1) absTop (Program.loop c1 b2)
              (evalP fuel b1 env) (absTop_sound _)
            simp only [validateP, Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨trivial, hb⟩
          rw [etail, ebody]
        · rw [if_neg hcond, if_neg hcond]

/-- **Main TV soundness theorem.**  Any control-flow rewrite the validator
    accepts preserves the whole-program fueled semantics on every input register
    file and every fuel budget. -/
theorem validate_sound (src tgt : Program) (h : validate src tgt = true) :
    ∀ fuel env, evalResult src fuel env = evalResult tgt fuel env := by
  intro fuel env
  exact validateP_sound fuel src absTop tgt env (absTop_sound env) h

/-! ## 8. The optimizer, and its non-vacuity (validator always accepts it) -/

/-- Optimize a program: fold the straight-line blocks (including loop-body
    blocks); reset the abstract state to `absTop` across every `seq`/`loop`
    boundary. -/
def optP (σ : AbsEnv) : Program → Program
  | .block b      => .block (optAux σ b)
  | .seq p q      => .seq (optP σ p) (optP absTop q)
  | .loop c body => .loop c (optP absTop body)

/-- Whole-program optimization from the empty abstract environment. -/
def optProg (p : Program) : Program := optP absTop p

/-- The validator accepts everything the optimizer produces. -/
theorem validateP_optP : ∀ (p : Program) (σ : AbsEnv),
    validateP σ p (optP σ p) = true := by
  intro p
  induction p with
  | block b => intro σ; simp only [optP, validateP]; exact validateAux_optAux σ b
  | seq p q ihp ihq =>
    intro σ
    simp only [optP, validateP, Bool.and_eq_true]
    exact ⟨ihp σ, ihq absTop⟩
  | loop c body ihb =>
    intro σ
    simp only [optP, validateP, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨trivial, ihb absTop⟩

/-- **Non-vacuity.**  The optimizer's output always passes the validator, so
    `validate_sound` is not vacuously true. -/
theorem opt_validates (p : Program) : validate p (optProg p) = true :=
  validateP_optP p absTop

/-- **Corollary: the loop-body optimization is semantics-preserving.** -/
theorem opt_sound (p : Program) :
    ∀ fuel env, evalResult p fuel env = evalResult (optProg p) fuel env :=
  validate_sound p (optProg p) (opt_validates p)

/-! ## 9. Non-vacuity witness: folding an `add` INSIDE the loop body

    The body is a block that materialises two constants and adds them; the
    optimizer folds the `add` to a literal WITHIN the loop body.  This is the
    intra-block const-fold acting inside a loop. -/

/-- Source: `loop (r0 ≠ 0) { r2 := 5; r3 := 6; r1 := r2 + r3 }`. -/
def loopFoldSrc : Program :=
  .loop 0 (.block [Instr.const 2 5, Instr.const 3 6, Instr.add 1 2 3])

/-- Optimized: the in-body `add` is folded to the literal `11`. -/
def loopFoldTgt : Program :=
  .loop 0 (.block [Instr.const 2 5, Instr.const 3 6, Instr.const 1 11])

/-- The optimizer, run on the loop, produces exactly the in-body folded program. -/
theorem opt_loopFold : optProg loopFoldSrc = loopFoldTgt := by decide

/-- …which the validator accepts. -/
theorem loopFold_accepted : validate loopFoldSrc loopFoldTgt = true := by decide

/-- …and it is a GENUINE rewrite (the third body instruction changed from `add`
    to `const`), so the acceptance is not trivial identity. -/
theorem loopFold_is_real_rewrite : loopFoldSrc ≠ loopFoldTgt := by decide

/-! ## 10. Adversarial counter-example: an unsound body rewrite is REJECTED and
    genuinely differs INSIDE the loop.

    The source loop body computes `r1 := r2 + r3` where `r2`/`r3` are unknown
    INPUTS (never assigned constants), so no fold is justified.  The bad target
    replaces the body with `r1 := 99`, a fold with no supporting constants. -/

/-- Source: `loop (r0 ≠ 0) { r1 := r2 + r3 }` (r2, r3 are inputs). -/
def advSrc : Program :=
  .loop 0 (.block [Instr.add 1 2 3])

/-- Bad target: the body is rewritten to the bogus constant `99`. -/
def advBadTgt : Program :=
  .loop 0 (.block [Instr.const 1 99])

/-- The validator REJECTS the unjustified in-loop fold. -/
theorem adv_rejected : validate advSrc advBadTgt = false := by decide

/-- A concrete input on which the loop actually runs its body: r0 = 1 (nonzero,
    so the loop is entered), r2 = 5, r3 = 6 (so the true body result is 11). -/
def advEnv : Env := fun x => if x = 2 then 5 else if x = 3 then 6 else 1

/-- …and rejection is warranted: with two units of fuel the loop runs its body
    once, so the source leaves `r1 = 5 + 6 = 11` loop the bad target leaves
    `r1 = 99`.  The observable genuinely changes INSIDE the loop. -/
theorem adv_semantics_differ :
    evalResult advSrc 2 advEnv 1 ≠ evalResult advBadTgt 2 advEnv 1 := by decide

/-! ## 11. Overflow-faithfulness inside the loop

    The value model wraps modulo 2^64, and the in-loop fold uses the SAME
    wrapping `+`.  Folding `maxU64 + 1` inside the body gives the literal `0`
    (the wrap), matching the backend; a fold that "ignored wrap" would be
    rejected exactly as in `mir_opt_tv`. -/

/-- The largest unsigned 64-bit word, `2^64 - 1`. -/
def maxU64 : Val := 0xFFFFFFFFFFFFFFFF

/-- Overflow is real: `maxU64 + 1` wraps to `0`. -/
theorem wrap_overflow : maxU64 + 1 = 0 := by decide

/-- Source loop body computes `r1 := maxU64 + 1` from two literals. -/
def ovLoopSrc : Program :=
  .loop 0 (.block [Instr.const 2 maxU64, Instr.const 3 1, Instr.add 1 2 3])

/-- The optimizer folds the in-body `add` to the WRAPPING literal `0`. -/
def ovLoopTgt : Program :=
  .loop 0 (.block [Instr.const 2 maxU64, Instr.const 3 1, Instr.const 1 0])

/-- The optimizer folds with overflow semantics inside the loop body. -/
theorem opt_ovLoop : optProg ovLoopSrc = ovLoopTgt := by decide

/-- …and the validator accepts the wrapping in-loop fold. -/
theorem ovLoop_accepted : validate ovLoopSrc ovLoopTgt = true := by decide

/-- A wrap-IGNORING in-loop fold (keeps `maxU64` instead of wrapping to `0`) is
    REJECTED. -/
def ovLoopBadTgt : Program :=
  .loop 0 (.block [Instr.const 2 maxU64, Instr.const 3 1, Instr.const 1 maxU64])

theorem ovLoop_bad_rejected : validate ovLoopSrc ovLoopBadTgt = false := by decide

/-! ## 12. Disclosed axiom footprint -/

#print axioms validate_sound
#print axioms opt_sound
#print axioms opt_loopFold
#print axioms adv_rejected
#print axioms adv_semantics_differ
#print axioms wrap_overflow

end MirLoopTv
