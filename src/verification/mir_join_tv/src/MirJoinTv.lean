/-
  MirJoinTv — DO-333 translation-validation soundness for PRECISE
  CFG-join constant-propagation over a structured MIR fragment.

  Sibling of `src/verification/mir_opt_tv/src/MirOptTv.lean`. That development
  proved TV soundness for straight-line and structured control flow, but at every
  branch merge it threw away ALL tracked constants (`absStepP σ (ite …) = absTop`,
  a deliberately conservative over-approximation). This file closes exactly that
  precision gap: at a branch merge we compute the JOIN (meet in the "known
  constants" lattice) of the two arms' abstract states, so a register that BOTH
  arms leave holding the SAME constant is still known to be that constant AFTER
  the branch — and a constant-propagation rewrite in the code following the merge
  is then justified and proved semantics-preserving.

  VALUE MODEL: machine words are FAITHFUL 64-bit two's-complement (`BitVec 64`);
  `+` wraps modulo 2^64 exactly like the backend's `add`. The const-fold that the
  joined state licenses uses the SAME wrapping `+`, so the folded literal is
  definitionally what the hardware computes (overflow section §12 makes this a
  theorem, not a hope).

  THE JOIN (§4). For abstract states `s1 s2 : Reg → Option Val`,
    `join s1 s2 r = some c`  iff  `s1 r = some c AND s2 r = some c`
  (both arms agree on the same constant `c`); otherwise `none` (⊤ / unknown).
  Galois-style soundness: if `s1` soundly describes a concrete state, so does the
  join; likewise for `s2` (`join_sound_left` / `join_sound_right`). Because the
  concrete execution flows through exactly ONE arm, and the joined state is sound
  for the result of EITHER arm, the joined state soundly describes the merged
  concrete state regardless of which branch ran (`absStepP_sound`, `ite` case).

  MODELLED (in scope):
    * straight-line blocks: `const`/`add`/`copy` over `BitVec 64`,
    * structured control flow `Program = block | seq | ite` (no arbitrary goto),
    * a per-compile translation validator `validateProg : Program → Program → Bool`
      threading the abstract state, using the JOIN at `ite` merges,
    * the const-prop optimizer `optProg`, proved to always pass the validator.

  OUT OF SCOPE (honest_scope): loops / `while` (this is a SINGLE meet level — one
  branch join, no fixpoint iteration), φ-nodes / general CFG merges beyond the two
  structured `ite` arms, register allocation, instruction selection, memory/calls,
  and widths/signedness other than 64-bit wrapping `add`. Dead-branch elimination
  (a different optimization) is intentionally NOT modelled here; the sibling file
  covers it. This file's contribution is the branch JOIN and nothing else.

  All theorems use the Lean core library only (no Mathlib) and no proof-trust
  bypasses: the repo's `check-lean-proofs.shs` TRUST_RE gate finds nothing, and
  `#print axioms` (§13) shows only `propext` plus Lean's foundational axioms.
-/
namespace MirJoinTv

/-! ## 1. Syntax of the MIR fragment -/

/-- A virtual register is identified by a natural number. -/
abbrev Reg : Type := Nat

/-- Machine values are 64-bit words; `+` wraps modulo 2^64 (see file header). -/
abbrev Val : Type := BitVec 64

/-- Straight-line MIR instructions over the constant-fold/copy-prop subset. -/
inductive Instr where
  /-- `const dst v` : write literal `v` into register `dst`. -/
  | const : Reg → Val → Instr
  /-- `add dst a b` : `dst := a + b`. -/
  | add   : Reg → Reg → Reg → Instr
  /-- `copy dst src` : `dst := src`. -/
  | copy  : Reg → Reg → Instr
  deriving DecidableEq

/-- A straight-line basic block is a list of instructions. -/
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

/-- Whole-block semantics: fold the per-instruction step left-to-right. -/
def eval (p : Mir) (env : Env) : Env :=
  p.foldl evalInstr env

/-! ## 3. Abstract constant environment (what the checker/optimizer tracks) -/

/-- Abstract environment: `some c` = "provably holds constant `c` here";
    `none` = "unknown" (the ⊤ element of the known-constants lattice). -/
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
    the abstraction claims constant really holds that value (`σ ⊑ γ(env)`). -/
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

/-! ## 4. THE JOIN — precise merge of two abstract states (this file's payload)

    `join s1 s2` keeps a register's constant ONLY when BOTH `s1` and `s2` assign
    it the SAME constant; any disagreement or unknown collapses to `none` (⊤). -/

/-- The join / merge of two abstract states. -/
def join (s1 s2 : AbsEnv) : AbsEnv := fun r =>
  match s1 r, s2 r with
  | some a, some b => if a = b then some a else none
  | _, _           => none

/-- **Join soundness (left).** If `s1` soundly describes `env`, so does the join:
    every constant the join asserts is one `s1` also asserts (with equal value),
    hence really holds in `env`. -/
theorem join_sound_left (s1 s2 : AbsEnv) (env : Env)
    (h : absSound s1 env) : absSound (join s1 s2) env := by
  intro r v hr
  cases h1 : s1 r with
  | none => simp [join, h1] at hr
  | some a =>
    cases h2 : s2 r with
    | none => simp [join, h1, h2] at hr
    | some b =>
      simp only [join, h1, h2] at hr
      by_cases hab : a = b
      · rw [if_pos hab] at hr
        simp only [Option.some.injEq] at hr
        rw [← hr]; exact h r a h1
      · rw [if_neg hab] at hr
        simp at hr

/-- **Join soundness (right).** Symmetric: if `s2` soundly describes `env`, so
    does the join (the retained value equals `s2`'s, since the arms agreed). -/
theorem join_sound_right (s1 s2 : AbsEnv) (env : Env)
    (h : absSound s2 env) : absSound (join s1 s2) env := by
  intro r v hr
  cases h1 : s1 r with
  | none => simp [join, h1] at hr
  | some a =>
    cases h2 : s2 r with
    | none => simp [join, h1, h2] at hr
    | some b =>
      simp only [join, h1, h2] at hr
      by_cases hab : a = b
      · rw [if_pos hab] at hr
        simp only [Option.some.injEq] at hr
        rw [← hr, hab]; exact h r b h2
      · rw [if_neg hab] at hr
        simp at hr

/-! ## 5. The straight-line translation validator -/

/-- Per-instruction check: is rewriting source `s` into target `t` justified by
    the known constants `σ`? Accept iff `t` is identical to `s`, or `s`/`t` is a
    licensed constant-fold (`add` of two known constants) / copy-of-known-constant. -/
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

/-- Lockstep validation of two blocks, threading the abstract state (advanced by
    the SOURCE instructions). -/
def validateAux (σ : AbsEnv) : Mir → Mir → Bool
  | [],      []      => true
  | s :: ss, t :: ts => checkInstr σ s t && validateAux (absStep σ s) ss ts
  | _,       _       => false

/-- The straight-line validator: validate from the empty abstract environment. -/
def validate (src tgt : Mir) : Bool := validateAux absTop src tgt

/-! ## 6. Straight-line soundness -/

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

/-- **Straight-line TV soundness.** Any accepted block rewrite preserves the
    whole-block semantics on every input. (`#print axioms` target of the gate.) -/
theorem validate_sound (src tgt : Mir) (h : validate src tgt = true) :
    ∀ env, eval src env = eval tgt env := by
  intro env
  unfold eval
  exact validateAux_sound absTop src tgt env (absTop_sound env) h

/-! ## 7. Straight-line optimizer and its non-vacuity -/

/-- Optimize one instruction under the known constants `σ`. -/
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

/-- Optimize a whole block, threading the abstract state. -/
def optAux (σ : AbsEnv) : Mir → Mir
  | []      => []
  | i :: is => optInstr σ i :: optAux (absStep σ i) is

/-- Constant-fold + copy-propagation over a straight-line block. -/
def opt (p : Mir) : Mir := optAux absTop p

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

theorem validateAux_optAux (σ : AbsEnv) (p : Mir) :
    validateAux σ p (optAux σ p) = true := by
  induction p generalizing σ with
  | nil => rfl
  | cons i is ih =>
    unfold optAux validateAux
    rw [checkInstr_optInstr σ i]
    simp only [Bool.true_and]
    exact ih (absStep σ i)

theorem opt_validates (p : Mir) : validate p (opt p) = true :=
  validateAux_optAux absTop p

theorem opt_sound (p : Mir) : ∀ env, eval p env = eval (opt p) env :=
  validate_sound p (opt p) (opt_validates p)

/-! ## 8. Structured control flow -/

/-- Structured control-flow program over straight-line MIR blocks. -/
inductive Program where
  /-- A straight-line basic block. -/
  | block : Mir → Program
  /-- Sequential composition: run `p`, then `q`. -/
  | seq   : Program → Program → Program
  /-- Branch on register `c`: nonzero → `t`, zero → `e`. -/
  | ite   : Reg → Program → Program → Program
  deriving DecidableEq

/-- Control-flow semantics: a total state transformer (no loops ⇒ no fuel). -/
def evalP : Program → Env → Env
  | .block b, env => b.foldl evalInstr env
  | .seq p q, env => evalP q (evalP p env)
  | .ite c t e, env => if env c ≠ 0 then evalP t env else evalP e env

/-! ## 9. Abstract transfer over control flow — PRECISE at merges

    Unlike the sibling file (which used `absTop` after every branch), the `ite`
    case here JOINS the two arms' abstract states, so constants both arms agree on
    survive the merge. `seq` threads the (possibly joined) state into its tail. -/

/-- Fold the abstract transfer across a straight-line block. -/
def absStepP (σ : AbsEnv) : Program → AbsEnv
  | .block b => b.foldl absStep σ
  | .seq p q => absStepP (absStepP σ p) q
  | .ite _ t e => join (absStepP σ t) (absStepP σ e)

/-- Soundness of the block-level abstract fold (iterated `absStep_sound`). -/
theorem absFold_sound : ∀ (b : Mir) (σ : AbsEnv) (env : Env),
    absSound σ env → absSound (b.foldl absStep σ) (b.foldl evalInstr env) := by
  intro b
  induction b with
  | nil => intro σ env h; simpa using h
  | cons i is ih =>
    intro σ env h
    simp only [List.foldl_cons]
    exact ih (absStep σ i) (evalInstr env i) (absStep_sound σ env i h)

/-- **The join makes the merge sound.** The program-level abstract transfer
    preserves soundness across `evalP`. The `ite` case is the payload: concrete
    execution takes exactly one arm, and the JOIN is sound for the result of
    EITHER arm (`join_sound_left` / `join_sound_right`), so it soundly describes
    the merged state no matter which branch ran. -/
theorem absStepP_sound : ∀ (p : Program) (σ : AbsEnv) (env : Env),
    absSound σ env → absSound (absStepP σ p) (evalP p env) := by
  intro p
  induction p with
  | block b => intro σ env h; simp only [absStepP, evalP]; exact absFold_sound b σ env h
  | seq p q ihp ihq =>
    intro σ env h
    simp only [absStepP, evalP]
    exact ihq (absStepP σ p) (evalP p env) (ihp σ env h)
  | ite c t e iht ihe =>
    intro σ env h
    simp only [absStepP, evalP]
    by_cases hc : env c ≠ 0
    · rw [if_pos hc]
      exact join_sound_left (absStepP σ t) (absStepP σ e) (evalP t env) (iht σ env h)
    · rw [if_neg hc]
      exact join_sound_right (absStepP σ t) (absStepP σ e) (evalP e env) (ihe σ env h)

/-! ## 10. The control-flow validator

    `block`/`block` reuses `validateAux`; `seq`/`seq` validates componentwise,
    threading `absStepP` (so a rewrite in the tail is checked under the JOINED
    state produced by a preceding `ite`); `ite`/`ite` validates the arms under the
    pre-branch state and requires the same condition register. Everything that
    makes the join PAY OFF happens in the `seq` tail, checked below. -/
def validateP (σ : AbsEnv) : Program → Program → Bool
  | .block b1, tgt =>
      match tgt with
      | .block b2 => validateAux σ b1 b2
      | _ => false
  | .seq p1 q1, tgt =>
      match tgt with
      | .seq p2 q2 => validateP σ p1 p2 && validateP (absStepP σ p1) q1 q2
      | _ => false
  | .ite c t e, tgt =>
      match tgt with
      | .ite c' t' e' => decide (c = c') && validateP σ t t' && validateP σ e e'
      | _ => false

/-- The control-flow validator: validate from the empty abstract environment. -/
def validateProg (src tgt : Program) : Bool := validateP absTop src tgt

/-! ## 11. Control-flow soundness -/

theorem validateP_sound : ∀ (src : Program) (σ : AbsEnv) (tgt : Program) (env : Env),
    absSound σ env → validateP σ src tgt = true → evalP src env = evalP tgt env := by
  intro src
  induction src with
  | block b1 =>
    intro σ tgt env hσ h
    cases tgt with
    | block b2 =>
      simp only [evalP]
      exact validateAux_sound σ b1 b2 env hσ (by simpa only [validateP] using h)
    | seq _ _ => simp [validateP] at h
    | ite _ _ _ => simp [validateP] at h
  | seq p1 q1 ihp ihq =>
    intro σ tgt env hσ h
    cases tgt with
    | block _ => simp [validateP] at h
    | ite _ _ _ => simp [validateP] at h
    | seq p2 q2 =>
      simp only [validateP, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      simp only [evalP]
      have e1 : evalP p1 env = evalP p2 env := ihp σ p2 env hσ h1
      have hσ' : absSound (absStepP σ p1) (evalP p1 env) := absStepP_sound p1 σ env hσ
      have e2 : evalP q1 (evalP p1 env) = evalP q2 (evalP p1 env) :=
        ihq (absStepP σ p1) q2 (evalP p1 env) hσ' h2
      rw [e2, e1]
  | ite c t e iht ihe =>
    intro σ tgt env hσ h
    cases tgt with
    | block _ => simp [validateP] at h
    | seq _ _ => simp [validateP] at h
    | ite c' t' e' =>
      simp only [validateP, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hcc, ht⟩, he⟩ := h
      subst hcc
      simp only [evalP]
      have et : evalP t env = evalP t' env := iht σ t' env hσ ht
      have ee : evalP e env = evalP e' env := ihe σ e' env hσ he
      rw [et, ee]

/-- **Main control-flow TV soundness (join-guarded).** Any control-flow rewrite
    the validator accepts — including const-prop in code AFTER a branch merge,
    justified by the JOINED abstract state — preserves the whole-program
    semantics on every input. -/
theorem validateProg_sound (src tgt : Program) (h : validateProg src tgt = true) :
    ∀ env, evalP src env = evalP tgt env := by
  intro env
  exact validateP_sound src absTop tgt env (absTop_sound env) h

/-! ## 12. Control-flow optimizer and its non-vacuity -/

/-- Optimize a program, threading the abstract state (JOINED across `ite`). A
    const-fold in a `seq` tail is licensed by the join of the preceding branch. -/
def optP (σ : AbsEnv) : Program → Program
  | .block b => .block (optAux σ b)
  | .seq p q => .seq (optP σ p) (optP (absStepP σ p) q)
  | .ite c t e => .ite c (optP σ t) (optP σ e)

/-- Whole-program optimization from the empty abstract environment. -/
def optProg (p : Program) : Program := optP absTop p

theorem validateP_optP : ∀ (p : Program) (σ : AbsEnv),
    validateP σ p (optP σ p) = true := by
  intro p
  induction p with
  | block b => intro σ; simp only [optP, validateP]; exact validateAux_optAux σ b
  | seq p q ihp ihq =>
    intro σ
    simp only [optP, validateP, Bool.and_eq_true]
    exact ⟨ihp σ, ihq (absStepP σ p)⟩
  | ite c t e iht ihe =>
    intro σ
    simp only [optP, validateP, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨trivial, iht σ⟩, ihe σ⟩

theorem optProg_validates (p : Program) : validateProg p (optProg p) = true :=
  validateP_optP p absTop

/-- **Corollary: join-guarded const-prop is semantics-preserving.** -/
theorem optProg_sound (p : Program) : ∀ env, evalP p env = evalP (optProg p) env :=
  validateProg_sound p (optProg p) (optProg_validates p)

/-! ## 13. Non-vacuity: the join RECOVERS a constant both arms agree on

    Source branches on register 0 (an unknown INPUT), and BOTH arms set r1 := 5.
    The join therefore proves r1 = 5 after the merge, licensing the fold of the
    following `add r2 r1 r1` to the literal 10 — a rewrite the sibling file's
    absTop-at-merge could NOT justify. -/

/-- Both arms set r1 := 5; the tail computes r2 := r1 + r1. -/
def joinGoodSrc : Program :=
  .seq (.ite 0 (.block [Instr.const 1 5]) (.block [Instr.const 1 5]))
       (.block [Instr.add 2 1 1])

/-- Tail folded to r2 := 10, licensed by the joined state. -/
def joinGoodTgt : Program :=
  .seq (.ite 0 (.block [Instr.const 1 5]) (.block [Instr.const 1 5]))
       (.block [Instr.const 2 10])

/-- The joined abstract state after the merge DOES assert r1 = 5 (the concrete
    payoff of the join: agreement is preserved past the branch). -/
theorem join_recovers_const :
    absStepP absTop
      (Program.ite 0 (.block [Instr.const 1 5]) (.block [Instr.const 1 5])) 1
      = some 5 := by decide

/-- The validator accepts the join-guarded fold. -/
theorem join_good_accepted : validateProg joinGoodSrc joinGoodTgt = true := by decide

/-- The optimizer, run on the source, produces exactly that folded program —
    end-to-end evidence the join enables real const-prop after a merge. -/
theorem opt_joinGood : optProg joinGoodSrc = joinGoodTgt := by decide

/-- …and it is a genuine rewrite (the tail changes from `add` to `const`). -/
theorem join_good_is_real_rewrite : joinGoodSrc ≠ joinGoodTgt := by decide

/-! ## 14. Adversarial: arms DISAGREE ⇒ join asserts NOTHING ⇒ fold rejected

    Same shape, but the arms set r1 to DIFFERENT constants (5 vs 7). The join
    collapses r1 to `none`, so a tail that folds `add r2 r1 r1` to a literal is
    REJECTED — and rightly so, because it changes the result on the else path. -/

/-- Arms disagree on r1 (5 vs 7); tail still computes r2 := r1 + r1. -/
def joinBadSrc : Program :=
  .seq (.ite 0 (.block [Instr.const 1 5]) (.block [Instr.const 1 7]))
       (.block [Instr.add 2 1 1])

/-- Bad target: folds the tail to r2 := 10 as if r1 were provably 5. -/
def joinBadTgt : Program :=
  .seq (.ite 0 (.block [Instr.const 1 5]) (.block [Instr.const 1 7]))
       (.block [Instr.const 2 10])

/-- The join asserts NOTHING about r1 when the arms disagree. -/
theorem join_disagree_not_const :
    absStepP absTop
      (Program.ite 0 (.block [Instr.const 1 5]) (.block [Instr.const 1 7])) 1
      = none := by decide

/-- The validator REJECTS the unjustified post-merge fold. -/
theorem join_bad_rejected : validateProg joinBadSrc joinBadTgt = false := by decide

/-- …and rejection is warranted: on input r0 = 0 the else arm runs, so r1 = 7 and
    r2 = 14, but the bad target unconditionally gives r2 = 10. -/
theorem join_bad_semantics_differ :
    evalP joinBadSrc (fun _ => 0) 2 ≠ evalP joinBadTgt (fun _ => 0) 2 := by decide

/-- The optimizer correctly REFUSES to fold across the disagreeing merge: it
    leaves `joinBadSrc` unchanged (the tail `add` survives). -/
theorem opt_joinBad_is_identity : optProg joinBadSrc = joinBadSrc := by decide

/-! ## 15. Overflow-faithfulness of the join-guarded fold (the honesty payload)

    The value model is `BitVec 64` with wrapping `+`, so the fold the join
    licenses is the WRAPPING one. Both arms agree r1 := maxU64; the join proves
    r1 = maxU64 past the merge; the tail `add r2 r1 r1` folds to the wrapped
    literal `maxU64 + maxU64` (= 2^64 - 2), NOT to any non-wrapping value. -/

/-- The largest unsigned 64-bit word, `2^64 - 1`. -/
def maxU64 : Val := 0xFFFFFFFFFFFFFFFF

/-- Overflow is real: `maxU64 + maxU64` wraps (it is `< maxU64`, i.e. it did not
    saturate). Under unbounded `Int` this sum could not even be named by a single
    64-bit literal. -/
theorem join_fold_wraps : maxU64 + maxU64 ≠ maxU64 := by decide

/-- Both arms set r1 := maxU64; the tail computes r2 := r1 + r1. -/
def joinOvSrc : Program :=
  .seq (.ite 0 (.block [Instr.const 1 maxU64]) (.block [Instr.const 1 maxU64]))
       (.block [Instr.add 2 1 1])

/-- Correctly folded tail: the WRAPPING sum `maxU64 + maxU64`. -/
def joinOvGoodTgt : Program :=
  .seq (.ite 0 (.block [Instr.const 1 maxU64]) (.block [Instr.const 1 maxU64]))
       (.block [Instr.const 2 (maxU64 + maxU64)])

/-- Wrap-ignoring tail: keeps `maxU64` as if the add saturated. -/
def joinOvBadTgt : Program :=
  .seq (.ite 0 (.block [Instr.const 1 maxU64]) (.block [Instr.const 1 maxU64]))
       (.block [Instr.const 2 maxU64])

/-- The join-guarded WRAPPING fold is accepted (same `BitVec 64` `+`). -/
theorem join_ov_accepted : validateProg joinOvSrc joinOvGoodTgt = true := by decide

/-- The optimizer produces exactly the wrapped literal — folds with overflow. -/
theorem opt_joinOv : optProg joinOvSrc = joinOvGoodTgt := by decide

/-- The wrap-ignoring fold is REJECTED. -/
theorem join_ov_bad_rejected : validateProg joinOvSrc joinOvBadTgt = false := by decide

/-- …and rejection is warranted: the true (wrapped) result differs from maxU64. -/
theorem join_ov_semantics_differ :
    evalP joinOvSrc (fun _ => 0) 2 ≠ evalP joinOvBadTgt (fun _ => 0) 2 := by decide

/-! Compile-time demonstrations (kernel `#eval`, no proof obligations): the join
    recovers the agreed constant, and the wrapped fold's register 2 is 2^64 - 2. -/
#eval (maxU64 + maxU64 : Val)                    -- 0xfffffffffffffffe#64
#eval (evalP joinGoodSrc (fun _ => 0) 2)         -- 0x000000000000000a#64  (= 10)
#eval (evalP joinBadSrc (fun _ => 0) 2)          -- 0x000000000000000e#64  (= 14)

/-! ## 16. Disclosed axiom footprint -/

#print axioms validate_sound
#print axioms join_sound_left
#print axioms join_sound_right
#print axioms absStepP_sound
#print axioms validateProg_sound
#print axioms optProg_sound
#print axioms join_bad_rejected
#print axioms join_ov_bad_rejected

end MirJoinTv
