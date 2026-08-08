/-
  MirCseTv — DO-333 translation-validation soundness for MIR common-subexpression
  elimination (CSE).

  Plan: doc/03_plan/cert/formal_codegen_semantics_plan.md §(b) (translation
  validation of a MIR→MIR optimization). Sibling of `mir_opt_tv` (constant-fold +
  copy-prop) and `mir_dce_tv`; this project targets a DIFFERENT optimization —
  COMMON-SUBEXPRESSION ELIMINATION — with its own model, validator, optimizer and
  adversarial disproof.

  STRATEGY (translation validation). Rather than proving a whole compiler correct,
  we model a per-compile checker `validate : Mir → Mir → Bool` that the compiler
  runs after the CSE pass, and prove ANY rewrite it accepts is semantics-
  preserving (`validate_sound`). We then define the actual CSE optimizer `opt` and
  prove its output always passes the validator (`opt_validates`), so soundness is
  non-vacuous. Finally we exhibit an adversarial UNSOUND CSE — reuse across an
  intervening redefinition of an operand — and prove the validator REJECTS it and
  that it genuinely changes the observed result.

  THE OPTIMIZATION. CSE: when a later instruction recomputes an expression a
  register already holds, replace the recomputation with a COPY from that register.
  Concretely `add d2 a b` is rewritten to `copy d2 d1` when some register `d1`
  already holds `a + b` AND neither `a`, `b`, nor `d1` has been redefined since
  `d1` was computed. That "unchanged operands / holder" side condition is the whole
  correctness content, and is exactly what the validator enforces via a KILL on
  every redefinition.

  MODELLED (in scope):
    * Straight-line MIR: `List Instr` over virtual registers (`Nat`). Values are
      FAITHFUL 64-bit machine words (`BitVec 64`); `+` is native two's-complement
      addition modulo 2^64 — it WRAPS on overflow exactly like the backend's 64-bit
      `add`. CSE only moves an *identical* computation to a copy, so whatever the
      wrapping add produced is exactly what the copy reproduces: overflow-faithful
      by construction. Instructions: `const dst v`, `add dst a b`, `copy dst src`.
    * A denotational state-transformer semantics `eval : Mir → Env → Env`.
    * An available-expression abstract domain `Avail`, the optimizer `opt`, and the
      validator `validate`.

  OUT OF SCOPE (honest_scope; NOT assumed sound here): control flow
  (branches/loops), register allocation, instruction selection, the full MIR
  instruction set (calls/memory), CSE of `copy`/`const` (only `add` expressions are
  CSE'd), non-64-bit widths, and the interpreter path. Straight-line only — no
  `Program`/`ite` lift (that lives in the sibling `mir_opt_tv`).

  All theorems use the Lean core library only (no Mathlib) and no proof-trust
  bypasses — `check-lean-proofs.shs`'s TRUST_RE gate must find nothing. Adversarial
  facts are closed by the kernel `decide`, never `native_decide`.
-/
namespace MirCseTv

/-! ## 1. Syntax of the MIR fragment -/

/-- A virtual register is identified by a natural number. -/
abbrev Reg : Type := Nat

/-- Machine values are 64-bit words. `+` on `BitVec 64` wraps modulo 2^64,
    faithfully modelling the backend's overflow behaviour. -/
abbrev Val : Type := BitVec 64

/-- Straight-line MIR instructions over the CSE-relevant subset. -/
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

theorem upd_miss (env : Env) (r x : Reg) (v : Val) (h : x ≠ r) :
    upd env r v x = env x := by
  unfold upd; simp [h]

/-- One-step concrete execution of a single instruction. -/
def evalInstr (env : Env) (i : Instr) : Env :=
  match i with
  | .const d v => upd env d v
  | .add d a b => upd env d (env a + env b)
  | .copy d s  => upd env d (env s)

/-- Whole-fragment semantics: fold the per-instruction step left-to-right. -/
def eval (p : Mir) (env : Env) : Env :=
  p.foldl evalInstr env

/-! ## 3. Available-expression abstract domain

    `Avail` maps an ordered operand pair `(a, b)` to the register (if any) that
    currently holds the value `env a + env b`. `av a b = some d` is the abstract
    claim "register `d` provably equals `a + b` at this program point". This is the
    domain CSE reasons over: an `add d2 a b` may be turned into `copy d2 d1`
    precisely when `av a b = some d1`. -/

/-- Available expressions: for operand pair `(a,b)`, the register holding `a+b`. -/
abbrev Avail : Type := Reg → Reg → Option Reg

/-- Nothing is known to be available. -/
def availTop : Avail := fun _ _ => none

/-- Record that register `d` now holds the expression `a + b`. -/
def recordAvail (av : Avail) (a b d : Reg) : Avail :=
  fun x y => if x = a ∧ y = b then some d else av x y

/-- KILL every available expression invalidated by redefining register `d`:
    an entry `av x y = some r` is dropped if `d` is an operand (`x = d` or `y = d`,
    so `x + y` changed) OR the holder (`r = d`, so `r` no longer holds it). -/
def killAvail (av : Avail) (d : Reg) : Avail :=
  fun x y =>
    match av x y with
    | some r => if x = d ∨ y = d ∨ r = d then none else some r
    | none   => none

/-- Abstract transfer for one instruction. Every instruction redefines its `dst`,
    so first KILL `dst`; then `add d a b` (when neither operand is `d`) RECORDS
    that `d` holds `a + b`. `const`/`copy` record nothing new (only `add`
    expressions are CSE'd). -/
def availStep (av : Avail) (i : Instr) : Avail :=
  match i with
  | .const d _ => killAvail av d
  | .copy d _  => killAvail av d
  | .add d a b =>
      let av' := killAvail av d
      if a = d ∨ b = d then av' else recordAvail av' a b d

/-- Soundness of an available-expression map w.r.t. a concrete env: every recorded
    holder really equals the corresponding sum in the current register file. -/
def availSound (av : Avail) (env : Env) : Prop :=
  ∀ a b d, av a b = some d → env d = env a + env b

theorem availTop_sound (env : Env) : availSound availTop env := by
  intro a b d h
  simp [availTop] at h

/-- Inversion for `killAvail`: a surviving entry was present before, and none of
    its operands or holder is the killed register. -/
theorem killAvail_some {av : Avail} {d x y r : Reg}
    (h : killAvail av d x y = some r) :
    av x y = some r ∧ x ≠ d ∧ y ≠ d ∧ r ≠ d := by
  unfold killAvail at h
  cases hxy : av x y with
  | none => simp [hxy] at h
  | some r' =>
    simp only [hxy] at h
    by_cases hcond : x = d ∨ y = d ∨ r' = d
    · rw [if_pos hcond] at h; simp at h
    · rw [if_neg hcond] at h
      -- `cases hxy : av x y` abstracted `av x y` to `some r'` in the goal, so the
      -- first conjunct is now `some r' = some r`, which is exactly `h`.
      have hrr : r' = r := by simpa using h
      subst hrr
      exact ⟨h, fun hc => hcond (Or.inl hc),
               fun hc => hcond (Or.inr (Or.inl hc)),
               fun hc => hcond (Or.inr (Or.inr hc))⟩

/-- The abstract transfer preserves soundness across a concrete step. -/
theorem availStep_sound (av : Avail) (env : Env) (i : Instr)
    (h : availSound av env) : availSound (availStep av i) (evalInstr env i) := by
  cases i with
  | const d v =>
    intro x y r hr
    simp only [availStep] at hr
    obtain ⟨hav, hx, hy, hrr⟩ := killAvail_some hr
    simp only [evalInstr]
    rw [upd_miss env d r v hrr, upd_miss env d x v hx, upd_miss env d y v hy]
    exact h x y r hav
  | copy d s =>
    intro x y r hr
    simp only [availStep] at hr
    obtain ⟨hav, hx, hy, hrr⟩ := killAvail_some hr
    simp only [evalInstr]
    rw [upd_miss env d r _ hrr, upd_miss env d x _ hx, upd_miss env d y _ hy]
    exact h x y r hav
  | add d a b =>
    intro x y r hr
    simp only [evalInstr]
    by_cases hcond : a = d ∨ b = d
    · -- No new expression recorded; only the KILL survives.
      simp only [availStep, hcond, if_true] at hr
      obtain ⟨hav, hx, hy, hrr⟩ := killAvail_some hr
      rw [upd_miss env d r _ hrr, upd_miss env d x _ hx, upd_miss env d y _ hy]
      exact h x y r hav
    · -- `d := a + b` recorded, with `a ≠ d` and `b ≠ d`.
      have hade : a ≠ d := fun hc => hcond (Or.inl hc)
      have hbde : b ≠ d := fun hc => hcond (Or.inr hc)
      simp only [availStep] at hr
      rw [if_neg hcond] at hr
      simp only [recordAvail] at hr
      by_cases hxy : x = a ∧ y = b
      · rw [if_pos hxy] at hr
        obtain ⟨hxa, hyb⟩ := hxy
        have hrd : r = d := by simpa using hr.symm
        rw [hxa, hyb, hrd, upd_hit, upd_miss env d a _ hade, upd_miss env d b _ hbde]
      · rw [if_neg hxy] at hr
        obtain ⟨hav, hx, hy, hrr⟩ := killAvail_some hr
        rw [upd_miss env d r _ hrr, upd_miss env d x _ hx, upd_miss env d y _ hy]
        exact h x y r hav

/-! ## 4. The translation validator -/

/-- Per-instruction check: is rewriting source `s` into target `t` justified given
    the available expressions `av`?

    Accept iff EITHER
      * the CSE case: `s = add d a b`, `t = copy d src` where `av a b = some src`
        (the recomputation is replaced by a copy from the holder of `a + b`), OR
      * `t` is syntactically identical to `s` (no rewrite). -/
def checkInstr (av : Avail) (s t : Instr) : Bool :=
  match s, t with
  | .add d a b, .copy d' src =>
      decide (d = d') &&
        (match av a b with
         | some r => decide (src = r)
         | none   => false)
  | _, _ => decide (s = t)

/-- Lockstep validation, threading the available-expression map advanced by the
    SOURCE instructions (the abstraction describes the source's behaviour). -/
def validateAux (av : Avail) : Mir → Mir → Bool
  | [],      []      => true
  | s :: ss, t :: ts => checkInstr av s t && validateAux (availStep av s) ss ts
  | _,       _       => false

/-- The translation validator: run lockstep validation from the empty domain. -/
def validate (src tgt : Mir) : Bool := validateAux availTop src tgt

/-! ## 5. Soundness -/

theorem checkInstr_sound (av : Avail) (s t : Instr) (env : Env)
    (hav : availSound av env) (hc : checkInstr av s t = true) :
    evalInstr env s = evalInstr env t := by
  cases s with
  | const d v =>
    have heq : Instr.const d v = t := by
      simpa only [checkInstr, decide_eq_true_eq] using hc
    rw [heq]
  | copy d s' =>
    have heq : Instr.copy d s' = t := by
      simpa only [checkInstr, decide_eq_true_eq] using hc
    rw [heq]
  | add d a b =>
    cases t with
    | const d' v =>
      have heq : Instr.add d a b = Instr.const d' v := by
        simpa only [checkInstr, decide_eq_true_eq] using hc
      rw [heq]
    | add d' a' b' =>
      have heq : Instr.add d a b = Instr.add d' a' b' := by
        simpa only [checkInstr, decide_eq_true_eq] using hc
      rw [heq]
    | copy d' src =>
      -- The CSE case.
      simp only [checkInstr] at hc
      cases hab : av a b with
      | none => rw [hab] at hc; simp at hc
      | some r =>
        rw [hab] at hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨hdd, hsrc⟩ := hc
        subst hdd; subst hsrc
        simp only [evalInstr]
        -- `subst hsrc` renamed the holder `r` to `src`. Goal:
        -- upd env d (env a + env b) = upd env d (env src);
        -- availSound gives env src = env a + env b.
        have hr : env src = env a + env b := hav a b src hab
        rw [hr]

theorem validateAux_sound (av : Avail) (src tgt : Mir) (env : Env)
    (hav : availSound av env) (h : validateAux av src tgt = true) :
    src.foldl evalInstr env = tgt.foldl evalInstr env := by
  induction src generalizing av tgt env with
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
        checkInstr_sound av s t env hav hstep
      have hav' : availSound (availStep av s) (evalInstr env s) :=
        availStep_sound av env s hav
      simp only [List.foldl_cons]
      rw [← hstepEq]
      exact ih (availStep av s) ts (evalInstr env s) hav' hrest

/-- **Main TV soundness theorem.** Any CSE rewrite the validator accepts preserves
    the whole-fragment semantics on every input register file. -/
theorem validate_sound (src tgt : Mir) (h : validate src tgt = true) :
    ∀ env, eval src env = eval tgt env := by
  intro env
  unfold eval
  exact validateAux_sound availTop src tgt env (availTop_sound env) h

/-! ## 6. The CSE optimizer, and its non-vacuity -/

/-- Optimize one instruction: if `add d a b` recomputes an available expression
    (some register `r` holds `a + b`), replace it with `copy d r`. Otherwise leave
    it unchanged. -/
def optInstr (av : Avail) (i : Instr) : Instr :=
  match i with
  | .add d a b =>
      match av a b with
      | some r => .copy d r
      | none   => i
  | _ => i

/-- Optimize a whole fragment, threading the available-expression map. -/
def optAux (av : Avail) : Mir → Mir
  | []      => []
  | i :: is => optInstr av i :: optAux (availStep av i) is

/-- Common-subexpression elimination over a straight-line fragment. -/
def opt (p : Mir) : Mir := optAux availTop p

/-- The validator accepts every instruction the optimizer produces. -/
theorem checkInstr_optInstr (av : Avail) (i : Instr) :
    checkInstr av i (optInstr av i) = true := by
  cases i with
  | const d v => simp [checkInstr, optInstr]
  | copy d s  => simp [checkInstr, optInstr]
  | add d a b =>
    cases hab : av a b with
    | none =>
      have hopt : optInstr av (Instr.add d a b) = Instr.add d a b := by
        simp [optInstr, hab]
      rw [hopt]; simp [checkInstr]
    | some r =>
      have hopt : optInstr av (Instr.add d a b) = Instr.copy d r := by
        simp [optInstr, hab]
      rw [hopt]; simp [checkInstr, hab]

/-- Lockstep: the validator accepts the whole optimized fragment. -/
theorem validateAux_optAux (av : Avail) (p : Mir) :
    validateAux av p (optAux av p) = true := by
  induction p generalizing av with
  | nil => rfl
  | cons i is ih =>
    unfold optAux validateAux
    rw [checkInstr_optInstr av i]
    simp only [Bool.true_and]
    exact ih (availStep av i)

/-- **Non-vacuity.** The optimizer's output always passes the validator, so
    `validate_sound` is not vacuously true. -/
theorem opt_validates (p : Mir) : validate p (opt p) = true :=
  validateAux_optAux availTop p

/-- **Corollary: the CSE pass is semantics-preserving.** -/
theorem opt_sound (p : Mir) : ∀ env, eval p env = eval (opt p) env :=
  validate_sound p (opt p) (opt_validates p)

/-! ## 7. Adversarial counter-example: CSE across an intervening redefinition

    The whole correctness content of CSE is the "operands unchanged since the
    holder was computed" side condition. We exhibit a rewrite that VIOLATES it —
    reusing `r2 = r0 + r1` after `r0` has been reassigned — and prove the validator
    REJECTS it and that it changes the observed result. -/

/-- Source: r0 := 1; r1 := 2; r2 := r0 + r1 (=3); r0 := 10; r3 := r0 + r1 (=12).
    The redefinition `r0 := 10` sits BETWEEN the two `r0 + r1` computations, so the
    expression is NOT common: the second sum is `10 + 2 = 12`, not `1 + 2 = 3`. -/
def advSrc : Mir :=
  [Instr.const 0 1, Instr.const 1 2, Instr.add 2 0 1,
   Instr.const 0 10, Instr.add 3 0 1]

/-- Bad target: CSE the last `add 3 0 1` into `copy 3 2` (reuse the STALE r2=3),
    ignoring that r0 was reassigned. r3 becomes 3 instead of 12. -/
def advBadTgt : Mir :=
  [Instr.const 0 1, Instr.const 1 2, Instr.add 2 0 1,
   Instr.const 0 10, Instr.copy 3 2]

/-- The validator REJECTS reuse across the intervening redefinition: the KILL on
    `const 0 10` removed `(0,1)` from the available map, so no copy is justified. -/
theorem adv_rejected : validate advSrc advBadTgt = false := by decide

/-- …and rejection is warranted: register 3 is `12` in the source but `3` in the
    bad target — the unsound reuse genuinely changes the observed result. -/
theorem adv_semantics_differ :
    eval advSrc (fun _ => 0) 3 ≠ eval advBadTgt (fun _ => 0) 3 := by decide

/-! ## 8. Sanity: the honest CSE (no intervening redefinition) is accepted

    Same shape WITHOUT the `r0 := 10` in the middle: now `r0 + r1` really is a
    common subexpression, the fold is validator-accepted, it is what the optimizer
    produces, and it is a genuine rewrite (`add` becomes `copy`). This proves the
    validator is discriminating, not reject-everything. -/

/-- Source: r0 := 1; r1 := 2; r2 := r0 + r1; r3 := r0 + r1 — r0/r1 unchanged, so
    r2 and r3 are the same expression. -/
def goodSrc : Mir :=
  [Instr.const 0 1, Instr.const 1 2, Instr.add 2 0 1, Instr.add 3 0 1]

/-- Target: the second `add 3 0 1` CSE'd into `copy 3 2`. -/
def goodTgt : Mir :=
  [Instr.const 0 1, Instr.const 1 2, Instr.add 2 0 1, Instr.copy 3 2]

theorem good_accepted : validate goodSrc goodTgt = true := by decide

theorem opt_goodSrc : opt goodSrc = goodTgt := by decide

theorem good_is_real_rewrite : goodSrc ≠ goodTgt := by decide

/-- End-to-end: source and CSE'd target agree on the observed register 3 (both 3),
    confirming the accepted rewrite matches the backend. -/
theorem good_matches :
    eval goodSrc (fun _ => 0) 3 = eval goodTgt (fun _ => 0) 3 := by decide

/-! ## 9. Overflow-faithfulness note

    CSE never re-derives a value; it copies the one the wrapping `add` already
    produced. So overflow is preserved by construction. As a concrete witness, an
    `add` that wraps (`maxU64 + 1 = 0`) is CSE'd to a copy of that wrapped `0`. -/

/-- The largest unsigned 64-bit word, `2^64 - 1`. -/
def maxU64 : Val := 0xFFFFFFFFFFFFFFFF

/-- Overflow is real in this model: `maxU64 + 1` wraps to `0`. -/
theorem wrap_overflow : maxU64 + 1 = 0 := by decide

/-- Source: r0 := maxU64; r1 := 1; r2 := r0+r1 (wraps to 0); r3 := r0+r1 (also 0). -/
def ovSrc : Mir :=
  [Instr.const 0 maxU64, Instr.const 1 1, Instr.add 2 0 1, Instr.add 3 0 1]

/-- CSE'd target: `copy 3 2` — reproduces the wrapped `0`. -/
def ovTgt : Mir :=
  [Instr.const 0 maxU64, Instr.const 1 1, Instr.add 2 0 1, Instr.copy 3 2]

theorem ov_accepted : validate ovSrc ovTgt = true := by decide

theorem opt_ovSrc : opt ovSrc = ovTgt := by decide

/-- Both compute the wrapped result `0` in register 3 — the copy is faithful to the
    overflowing add. -/
theorem ov_matches :
    eval ovSrc (fun _ => 0) 3 = eval ovTgt (fun _ => 0) 3 := by decide

/-! Compile-time demonstrations (kernel evaluation, no axioms). -/
#eval (maxU64 + 1 : Val)               -- 0x0000000000000000#64
#eval (eval advSrc (fun _ => 0) 3)     -- 0x000000000000000c#64  (= 12)
#eval (eval advBadTgt (fun _ => 0) 3)  -- 0x0000000000000003#64  (= 3)

/-! ## 10. Disclosed axiom footprint -/

#print axioms validate_sound
#print axioms opt_sound
#print axioms adv_rejected
#print axioms adv_semantics_differ
#print axioms wrap_overflow

end MirCseTv
