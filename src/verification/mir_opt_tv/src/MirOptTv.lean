/-
  MirOptTv — DO-333 translation-validation soundness for a MIR→MIR optimization.

  Plan: doc/03_plan/cert/formal_codegen_semantics_plan.md §(b).

  This is the FIRST codegen semantic-preservation proof in the verification tree.
  It follows the *translation-validation* (TV) strategy chosen in the plan: rather
  than proving the whole compiler correct once and for all (CompCert style), we
  model a per-compile checker `validate : Mir → Mir → Bool` that the compiler
  would run after every optimization, and prove that ANY rewrite it accepts is
  semantics-preserving. We then define the actual optimization `opt` (constant
  folding + copy propagation over a straight-line MIR fragment) and prove it
  always produces validator-accepted output, so the soundness theorem is
  non-vacuous.

  MODELLED (in scope):
    * A straight-line MIR fragment: a `List Instr` over virtual registers (Nat),
      values are FAITHFUL 64-bit machine words (`BitVec 64`). `+` on `BitVec 64`
      is native two's-complement addition modulo 2^64 — it WRAPS on overflow,
      exactly like the real backend's 64-bit `add`. This closes the honesty gap
      that an unbounded-`Int` model would leave open: because the constant-fold
      folds `add (const a) (const b)` to `const (a + b)` using the SAME `BitVec 64`
      `+`, the folded literal is definitionally the value the backend computes,
      overflow included. Instructions: `const dst v`, `add dst a b`,
      `copy dst src` — exactly the constant-fold/copy-prop-relevant subset.
    * A denotational/state-transformer semantics `eval : Mir → Env → Env`.
    * The optimization `opt` and the validator `validate`.

  OUT OF SCOPE (deferred per plan §(b), NOT assumed sound here): register
  allocation, multi-ISA instruction selection, the full MIR instruction set
  (branches/calls/memory), signedness/width other than 64-bit wrapping add, and
  the interpreter execution path.

  All theorems proved with the Lean core library only (no Mathlib) and with no
  proof-trust bypasses — the repo's `check-lean-proofs.shs` TRUST_RE gate must
  find nothing.
-/
namespace MirOptTv

/-! ## 1. Syntax of the MIR fragment -/

/-- A virtual register is identified by a natural number. -/
abbrev Reg : Type := Nat

/-- Machine values are 64-bit words. `+`/`*` on `BitVec 64` wrap modulo 2^64,
    faithfully modelling the backend's overflow behaviour (see file header). -/
abbrev Val : Type := BitVec 64

/-- Straight-line MIR instructions over the constant-fold/copy-prop subset. -/
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

@[simp] theorem upd_hit (env : Env) (r : Reg) (v : Val) : upd env r v r = v := by
  unfold upd; simp

/-- One-step concrete execution of a single instruction. -/
def evalInstr (env : Env) (i : Instr) : Env :=
  match i with
  | .const d v => upd env d v
  | .add d a b => upd env d (env a + env b)
  | .copy d s  => upd env d (env s)

/-- Whole-fragment semantics: fold the per-instruction step left-to-right. -/
def eval (p : Mir) (env : Env) : Env :=
  p.foldl evalInstr env

/-! ## 3. Abstract constant environment (what the checker/optimizer tracks) -/

/-- Abstract environment: `some c` means "this register provably holds constant
    `c` at this program point"; `none` means "unknown". -/
abbrev AbsEnv : Type := Reg → Option Val

/-- The empty abstract environment: nothing is known. -/
def absTop : AbsEnv := fun _ => none

/-- Point update of the abstract environment. -/
def absUpd (σ : AbsEnv) (r : Reg) (v : Option Val) : AbsEnv :=
  fun x => if x = r then v else σ x

/-- Abstract transfer function for one instruction: propagate known constants. -/
def absStep (σ : AbsEnv) (i : Instr) : AbsEnv :=
  match i with
  | .const d v => absUpd σ d (some v)
  | .add d a b =>
      match σ a, σ b with
      | some va, some vb => absUpd σ d (some (va + vb))
      | _, _             => absUpd σ d none
  | .copy d s  => absUpd σ d (σ s)

/-- Soundness of an abstract environment w.r.t. a concrete one: every register
    the abstraction claims is a known constant really holds that value. -/
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
          -- env a = va and env b = vb by soundness of σ; and hr : va + vb = v.
          have hva : env a = va := h a va ha
          have hvb : env b = vb := h b vb hb
          -- After rewriting the concrete operands to their tracked constants the
          -- goal is `va + vb = v`; `hr` is literally that (same `BitVec 64` `+`).
          rw [hva, hvb]; exact hr
        · simp [hd] at hr ⊢; exact h r v hr
  | copy d s =>
    simp only [absStep, absUpd] at hr
    simp only [evalInstr, upd]
    by_cases hd : r = d
    · subst hd; simp at hr ⊢; exact h s v hr
    · simp [hd] at hr ⊢; exact h r v hr

/-! ## 4. The translation validator -/

/-- Per-instruction check: is rewriting source instruction `s` into target
    instruction `t` justified, given the known constants `σ` at this point?

    Accept iff EITHER
      * `t` is syntactically identical to `s` (no rewrite), OR
      * `s = add d a b`, `t = const d (va+vb)` where `σ` proves `a=va`, `b=vb`
        (constant folding), OR
      * `s = copy d src`, `t = const d c` where `σ` proves `src=c`
        (copy of a known constant / copy propagation to a literal). -/
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

/-- Lockstep validation of two fragments, threading the abstract environment
    (advanced by the SOURCE instructions, since the tracked constants describe
    the source program's behaviour). -/
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
    -- Source is `const`: only the fallback pattern applies, so `t` must equal it.
    have heq : Instr.const d v = t := by
      have h2 := hc
      simp only [checkInstr, decide_eq_true_eq] at h2
      exact h2
    rw [heq]
  | add d a b =>
    cases t with
    | const d' v =>
      -- Constant-folding case.
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
          -- Goal: evalInstr env (add d a b) = evalInstr env (const d (va+vb)).
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
      -- Copy-propagation-to-literal case.
      simp only [checkInstr] at hc
      cases hsrc : σ src with
      | none => rw [hsrc] at hc; simp at hc
      | some c =>
        rw [hsrc] at hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨hdd, hvv⟩ := hc
        subst hdd
        simp only [evalInstr]
        -- hvv : v = c and (soundness) env src = c, so env src = v.
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

/-- Core soundness over lists: if `validateAux σ src tgt` accepts and `σ` is sound
    for `env`, then running the two fragments from `env` yields the same final
    register file. -/
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
      -- Advance both folds by one step and apply the induction hypothesis.
      simp only [List.foldl_cons]
      rw [← hstepEq]
      exact ih (absStep σ s) ts (evalInstr env s) hσ' hrest

/-- **Main TV soundness theorem.** Any rewrite the validator accepts preserves
    the whole-fragment semantics on every input register file. -/
theorem validate_sound (src tgt : Mir) (h : validate src tgt = true) :
    ∀ env, eval src env = eval tgt env := by
  intro env
  unfold eval
  exact validateAux_sound absTop src tgt env (absTop_sound env) h

/-! ## 6. The optimization, and its non-vacuity (validator always accepts it) -/

/-- Optimize one instruction under the known-constant environment `σ`:
    fold `add` of two known constants to a literal, and turn a copy of a
    known-constant register into a literal. Otherwise leave it unchanged. -/
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

/-- Optimize a whole fragment, threading the abstract environment. -/
def optAux (σ : AbsEnv) : Mir → Mir
  | []      => []
  | i :: is => optInstr σ i :: optAux (absStep σ i) is

/-- Constant-fold + copy-propagation optimization over a straight-line fragment. -/
def opt (p : Mir) : Mir := optAux absTop p

/-- The validator accepts every instruction the optimizer produces. -/
theorem checkInstr_optInstr (σ : AbsEnv) (i : Instr) :
    checkInstr σ i (optInstr σ i) = true := by
  cases i with
  | const d v => simp [checkInstr, optInstr]
  | add d a b =>
    cases ha : σ a with
    | none =>
      -- optInstr returns the original `add`; checkInstr falls to identity.
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
        -- optInstr folds to `const d (va+vb)`; checkInstr verifies va+vb = va+vb.
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

/-- Lockstep: the validator accepts the whole optimized fragment. -/
theorem validateAux_optAux (σ : AbsEnv) (p : Mir) :
    validateAux σ p (optAux σ p) = true := by
  induction p generalizing σ with
  | nil => rfl
  | cons i is ih =>
    unfold optAux validateAux
    rw [checkInstr_optInstr σ i]
    simp only [Bool.true_and]
    exact ih (absStep σ i)

/-- **Non-vacuity.** The optimizer's output always passes the validator, so the
    (src, opt src) pair is a real, validator-accepted rewrite — `validate_sound`
    is not vacuously true. -/
theorem opt_validates (p : Mir) : validate p (opt p) = true :=
  validateAux_optAux absTop p

/-- **Corollary: the optimization is semantics-preserving.** Combining the TV
    soundness theorem with non-vacuity gives an unconditional guarantee that the
    fold+copy-prop pass preserves the meaning of every fragment. -/
theorem opt_sound (p : Mir) : ∀ env, eval p env = eval (opt p) env :=
  validate_sound p (opt p) (opt_validates p)

/-! ## 7. Adversarial counter-example (plan §(b) acceptance criterion 3)

    A deliberately UNSOUND rewrite: fold `add r0 r0 r1` (where r0=1, r1=2, so the
    true result is 3) to the wrong literal `const r2 99`. We prove the validator
    REJECTS it, and that the two fragments genuinely disagree — demonstrating the
    validator is discriminating, not trivially accept-everything. -/

/-- Source: r0 := 1; r1 := 2; r2 := r0 + r1   (so r2 = 3). -/
def advSrc : Mir :=
  [Instr.const 0 1, Instr.const 1 2, Instr.add 2 0 1]

/-- Bad target: same prologue but r2 folded to the WRONG constant 99. -/
def advBadTgt : Mir :=
  [Instr.const 0 1, Instr.const 1 2, Instr.const 2 99]

/-- The validator rejects the unsound fold. -/
theorem adv_rejected : validate advSrc advBadTgt = false := by
  decide

/-- The unsound rewrite really does change the observable result in register 2
    (3 vs 99), so rejection is warranted — the theorem is not vacuous. -/
theorem adv_semantics_differ :
    eval advSrc (fun _ => 0) 2 ≠ eval advBadTgt (fun _ => 0) 2 := by
  decide

/-- Sanity check that the validator is not merely "reject everything either":
    the honest fold of `advSrc` (to the correct constant 3) is ACCEPTED, and it
    is a genuine rewrite (the third instruction changes shape from `add` to
    `const`). -/
def advGoodTgt : Mir :=
  [Instr.const 0 1, Instr.const 1 2, Instr.const 2 3]

theorem adv_good_accepted : validate advSrc advGoodTgt = true := by
  decide

theorem adv_good_is_real_rewrite : advSrc ≠ advGoodTgt := by
  decide

/-- And the optimizer, run on `advSrc`, produces exactly that correct folded
    program — end-to-end evidence the modelled pass does the intended work. -/
theorem opt_advSrc : opt advSrc = advGoodTgt := by
  decide

/-! ## 8. Overflow-faithfulness: the model genuinely wraps (the honesty payload)

    This section is what makes the value model OVERFLOW-FAITHFUL rather than a
    convenient over-approximation. Over unbounded `Int` a folder that computed the
    *mathematical* sum would look correct, yet the real 64-bit backend wraps — so
    an `Int` proof would certify a fold the hardware does not actually perform.
    Here `Val = BitVec 64` and `+` wraps, so:

      * the wrap is a THEOREM of the model (`wrap_overflow`), and
      * the constant-fold that the validator accepts is the wrapping one — a fold
        that "ignores wrap" disagrees with the semantics on an overflowing input
        and is REJECTED (`ov_bad_rejected` + `ov_semantics_differ`). -/

/-- The largest unsigned 64-bit word, `2^64 - 1`. -/
def maxU64 : Val := 0xFFFFFFFFFFFFFFFF

/-- **Overflow is real in this model.** `maxU64 + 1` wraps to `0`, exactly as a
    hardware 64-bit `add` does. Under an unbounded-`Int` model this would instead
    be `2^64`, so this equation is precisely the fact the faithful model buys us. -/
theorem wrap_overflow : maxU64 + 1 = 0 := by decide

/-- Source: r0 := maxU64; r1 := 1; r2 := r0 + r1.  The backend computes r2 = 0
    (the add wraps). -/
def ovSrc : Mir :=
  [Instr.const 0 maxU64, Instr.const 1 1, Instr.add 2 0 1]

/-- Correct fold: the wrapping sum `maxU64 + 1 = 0`. -/
def ovGoodTgt : Mir :=
  [Instr.const 0 maxU64, Instr.const 1 1, Instr.const 2 0]

/-- Unsound fold that "ignores wrap": it keeps `maxU64` (as if `maxU64 + 1`
    saturated / stayed at the max) instead of wrapping to `0`. Over unbounded
    `Int` no single 64-bit literal can even name the true mathematical result
    `2^64`; the honest, representable answer is `0`, and anything else is wrong. -/
def ovBadTgt : Mir :=
  [Instr.const 0 maxU64, Instr.const 1 1, Instr.const 2 maxU64]

/-- The validator ACCEPTS the wrapping fold (its check `v = va + vb` uses the same
    `BitVec 64` `+`). -/
theorem ov_good_accepted : validate ovSrc ovGoodTgt = true := by decide

/-- The optimizer, run on the overflowing source, produces exactly the wrapping
    fold — end-to-end evidence the modelled pass folds with overflow semantics. -/
theorem opt_ovSrc : opt ovSrc = ovGoodTgt := by decide

/-- The validator REJECTS the wrap-ignoring fold. -/
theorem ov_bad_rejected : validate ovSrc ovBadTgt = false := by decide

/-- …and rejection is warranted: the wrap-ignoring target genuinely disagrees with
    the source on the overflowing input (r2 = 0 vs r2 = maxU64). This is the
    concrete overflowing witness `0xFFFFFFFFFFFFFFFF + 1` demanded by the plan. -/
theorem ov_semantics_differ :
    eval ovSrc (fun _ => 0) 2 ≠ eval ovBadTgt (fun _ => 0) 2 := by decide

/-- Cross-check that the wrapping fold really is the semantics of the source: both
    evaluate register 2 to `0`, i.e. the accepted fold matches the backend. -/
theorem ov_good_matches_src :
    eval ovSrc (fun _ => 0) 2 = eval ovGoodTgt (fun _ => 0) 2 := by decide

/-! Compile-time demonstrations (evaluate in the kernel, no axioms): `maxU64 + 1`
    wraps to 0, the source's register 2 is 0, and the wrap-ignoring target's is
    maxU64 (0xFFFF…FFFF) — printed by the `#eval`s below. -/
#eval (maxU64 + 1 : Val)                 -- 0x0000000000000000#64
#eval (eval ovSrc (fun _ => 0) 2)        -- 0x0000000000000000#64
#eval (eval ovBadTgt (fun _ => 0) 2)     -- 0xffffffffffffffff#64

/-! ## 9. Disclosed axiom footprint -/

#print axioms validate_sound
#print axioms wrap_overflow
#print axioms ov_bad_rejected

end MirOptTv
