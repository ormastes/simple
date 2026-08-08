/-
  MirDceTv — DO-333 translation-validation soundness for MIR DEAD-CODE /
  DEAD-STORE ELIMINATION.

  Plan: doc/03_plan/cert/formal_codegen_semantics_plan.md §(b).

  This is the SECOND codegen semantic-preservation proof in the verification tree
  (companion to `mir_opt_tv`, which covers constant-fold + copy-prop). It follows
  the same *translation-validation* (TV) strategy: rather than proving a whole
  compiler correct once, we model a per-compile checker `validate : Mir → Mir →
  Bool` that the compiler runs after every DCE pass, and prove that ANY rewrite it
  accepts is semantics-preserving w.r.t. the value of a designated RESULT register.
  We then define the actual pass `dce` and prove its output always passes the
  validator, so the soundness theorem is non-vacuous.

  MODELLED (in scope):
    * A straight-line MIR fragment: a `List Instr` over virtual registers (Nat).
      Values are FAITHFUL 64-bit machine words (`BitVec 64`); `+` wraps modulo
      2^64 exactly like the backend's `add`. Instructions: `const dst v`,
      `add dst a b`, `copy dst src` — each writes exactly ONE register.
    * A state-transformer semantics `eval : Mir → Env → Env`, observed through
      `evalResult p env = (eval p env) resultReg` (the final value of a single
      designated result register — the program's observable output).
    * Backward LIVENESS (`liveIn`): a register is live at a point if some later
      instruction reads it before it is overwritten, or it is the result register
      at program end.
    * The DCE pass `dce` (drop every instruction whose written register is dead in
      the remaining suffix and is not the result) and the validator `validate`.

  OUT OF SCOPE (deferred per plan §(b), NOT assumed sound here): register
  allocation, multi-ISA selection, the full MIR instruction set
  (branches/calls/memory — hence liveness here is straight-line only, no join
  lattice), multi-output observation (a single result register is observed), and
  the interpreter execution path.

  All theorems proved with the Lean core library only (no Mathlib) and with no
  proof-trust bypasses.
-/
namespace MirDceTv

/-! ## 1. Syntax of the MIR fragment -/

/-- A virtual register is identified by a natural number. -/
abbrev Reg : Type := Nat

/-- Machine values are 64-bit words; `+` wraps modulo 2^64 (backend-faithful). -/
abbrev Val : Type := BitVec 64

/-- Straight-line MIR instructions; each writes exactly one register. -/
inductive Instr where
  /-- `const dst v` : write literal `v` into register `dst`. -/
  | const : Reg → Val → Instr
  /-- `add dst a b` : `dst := a + b`. -/
  | add   : Reg → Reg → Reg → Instr
  /-- `copy dst src` : `dst := src`. -/
  | copy  : Reg → Reg → Instr
  deriving DecidableEq

/-- A MIR fragment is a straight-line list of instructions. -/
abbrev Mir : Type := List Instr

/-- The single register whose final value is the observable output. -/
def resultReg : Reg := 0

/-- The register written by an instruction (all instructions write exactly one). -/
def writes : Instr → Reg
  | .const d _ => d
  | .add d _ _ => d
  | .copy d _  => d

/-- Does instruction `i` read register `r`? -/
def readsReg : Instr → Reg → Bool
  | .const _ _, _ => false
  | .add _ a b, r => decide (r = a) || decide (r = b)
  | .copy _ s,  r => decide (r = s)

/-! ## 2. Concrete semantics -/

/-- A register file maps every register to its current value. -/
abbrev Env : Type := Reg → Val

/-- Point update of a register file. -/
def upd (env : Env) (r : Reg) (v : Val) : Env :=
  fun x => if x = r then v else env x

@[simp] theorem upd_hit (env : Env) (r : Reg) (v : Val) : upd env r v r = v := by
  unfold upd; simp

theorem upd_miss (env : Env) (r : Reg) (v : Val) (x : Reg) (h : x ≠ r) :
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

@[simp] theorem eval_nil (env : Env) : eval [] env = env := rfl

theorem eval_cons (i : Instr) (rest : Mir) (env : Env) :
    eval (i :: rest) env = eval rest (evalInstr env i) := by
  unfold eval; rw [List.foldl_cons]

/-- The observable output: the final value of the result register. -/
def evalResult (p : Mir) (env : Env) : Val := (eval p env) resultReg

/-- A register untouched by `i` keeps its value across the step. -/
theorem evalInstr_other (env : Env) (i : Instr) (r : Reg) (h : r ≠ writes i) :
    evalInstr env i r = env r := by
  cases i with
  | const d v => simp only [evalInstr]; exact upd_miss _ _ _ _ (by simpa [writes] using h)
  | add d a b => simp only [evalInstr]; exact upd_miss _ _ _ _ (by simpa [writes] using h)
  | copy d s  => simp only [evalInstr]; exact upd_miss _ _ _ _ (by simpa [writes] using h)

/-! ## 3. Backward liveness -/

/-- `liveIn p r` : is register `r` live at the START of fragment `p`?  Backward
    dataflow: at the end only the result register is live; an instruction makes its
    read-registers live and kills its written register (unless also read). -/
def liveIn : Mir → Reg → Bool
  | [],        r => decide (r = resultReg)
  | i :: rest, r => readsReg i r || (decide (r ≠ writes i) && liveIn rest r)

/-- An instruction is DEAD relative to the suffix `rest` if its written register is
    not live afterwards (its result is never observed). -/
def isDead (i : Instr) (rest : Mir) : Bool := ! liveIn rest (writes i)

/-! ## 4. Agreement and the core liveness lemma -/

/-- Two environments AGREE on the register set `S` if they coincide there. -/
def agree (S : Reg → Bool) (e1 e2 : Env) : Prop := ∀ r, S r = true → e1 r = e2 r

/-- **Core liveness lemma.** If two environments agree on everything live at the
    start of `p`, then running `p` from each yields the SAME result-register value.
    (Observational equivalence is determined by the live-in set.) -/
theorem eval_result_agree (p : Mir) :
    ∀ (e1 e2 : Env), agree (liveIn p) e1 e2 →
      (eval p e1) resultReg = (eval p e2) resultReg := by
  induction p with
  | nil =>
    intro e1 e2 h
    simp only [eval_nil]
    exact h resultReg (by simp [liveIn])
  | cons i rest ih =>
    intro e1 e2 h
    rw [eval_cons, eval_cons]
    apply ih
    intro r hr
    -- Goal: evalInstr e1 i r = evalInstr e2 i r, given liveIn rest r = true.
    cases hdec : decide (r = writes i) with
    | true =>
      have hw : r = writes i := of_decide_eq_true hdec
      subst hw
      -- r is the written register; the written value depends only on read regs,
      -- on which e1,e2 agree (reads ⊆ liveIn (i::rest)).
      cases i with
      | const d v => simp [evalInstr, writes]
      | add d a b =>
        have ha : e1 a = e2 a := h a (by simp [liveIn, readsReg])
        have hb : e1 b = e2 b := h b (by simp [liveIn, readsReg])
        simp only [evalInstr, writes, upd_hit]; rw [ha, hb]
      | copy d s =>
        have hs : e1 s = e2 s := h s (by simp [liveIn, readsReg])
        simp only [evalInstr, writes, upd_hit]; rw [hs]
    | false =>
      have hw : r ≠ writes i := of_decide_eq_false hdec
      rw [evalInstr_other e1 i r hw, evalInstr_other e2 i r hw]
      -- r is untouched; it is live-in for (i::rest) since live in rest and unwritten.
      apply h r
      show liveIn (i :: rest) r = true
      unfold liveIn
      rw [hr]
      simp [hw]

/-! ## 5. The translation validator -/

/-- Lockstep validation of source vs. target.  Walking the source, every DEAD head
    instruction MUST be dropped (target unchanged); every LIVE head instruction must
    appear identically as the next target instruction. -/
def validateAux : Mir → Mir → Bool
  | [],        []        => true
  | [],        _ :: _    => false
  | i :: ss,   tgt       =>
      if isDead i ss then
        validateAux ss tgt
      else
        match tgt with
        | []      => false
        | t :: ts => (i == t) && validateAux ss ts

/-- The DCE translation validator. -/
def validate (src tgt : Mir) : Bool := validateAux src tgt

/-! ## 6. Soundness -/

/-- Dropping a dead head instruction does not change the result value: the killed
    write is invisible to the live-in set of the remaining suffix. -/
theorem drop_dead_result (i : Instr) (ss : Mir) (env : Env)
    (hd : isDead i ss = true) :
    (eval (i :: ss) env) resultReg = (eval ss env) resultReg := by
  rw [eval_cons]
  -- eval ss (evalInstr env i) vs eval ss env: agree on liveIn ss.
  apply eval_result_agree ss (evalInstr env i) env
  intro r hr
  -- r live in ss ⇒ r ≠ writes i (else isDead would be false) ⇒ untouched.
  have hne : r ≠ writes i := by
    intro hEq
    subst hEq
    -- liveIn ss (writes i) = true contradicts isDead i ss = true.
    unfold isDead at hd
    rw [hr] at hd
    exact absurd hd (by decide)
  exact evalInstr_other env i r hne

/-- Core list soundness: any lockstep-accepted rewrite preserves the result value
    on EVERY input register file. -/
theorem validateAux_sound (src tgt : Mir) (h : validateAux src tgt = true) :
    ∀ env, (eval src env) resultReg = (eval tgt env) resultReg := by
  induction src generalizing tgt with
  | nil =>
    intro env
    cases tgt with
    | nil => rfl
    | cons t ts => simp [validateAux] at h
  | cons i ss ih =>
    intro env
    cases hdead : isDead i ss with
    | true =>
      -- Dead head: validateAux drops it (target unchanged).
      have h' : validateAux ss tgt = true := by
        have e : validateAux (i :: ss) tgt = validateAux ss tgt := by
          simp [validateAux, hdead]
        rwa [e] at h
      rw [drop_dead_result i ss env hdead]
      exact ih tgt h' env
    | false =>
      -- Live head: must match the next target instruction identically.
      cases tgt with
      | nil =>
        have e : validateAux (i :: ss) [] = false := by simp [validateAux, hdead]
        rw [e] at h; exact absurd h (by decide)
      | cons t ts =>
        have e : validateAux (i :: ss) (t :: ts) = ((i == t) && validateAux ss ts) := by
          simp [validateAux, hdead]
        rw [e] at h
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨hit, hrest⟩ := h
        subst hit
        rw [eval_cons, eval_cons]
        exact ih ts hrest (evalInstr env i)

/-- **Main TV soundness theorem.** Any rewrite the validator accepts preserves the
    observable result on every input register file. -/
theorem validate_sound (src tgt : Mir) (h : validate src tgt = true) :
    ∀ env, evalResult src env = evalResult tgt env := by
  intro env
  unfold evalResult
  exact validateAux_sound src tgt h env

/-! ## 7. The DCE pass and non-vacuity -/

/-- Dead-code / dead-store elimination: drop every instruction whose written
    register is dead in the remaining suffix. -/
def dce : Mir → Mir
  | []      => []
  | i :: ss => if isDead i ss then dce ss else i :: dce ss

/-- **Non-vacuity.** The DCE pass's output always passes the validator, so
    `validate_sound` is not vacuously true. -/
theorem dce_validates (p : Mir) : validate p (dce p) = true := by
  unfold validate
  induction p with
  | nil => rfl
  | cons i ss ih =>
    cases hdead : isDead i ss with
    | true =>
      have hdce : dce (i :: ss) = dce ss := by simp [dce, hdead]
      have hva : validateAux (i :: ss) (dce ss) = validateAux ss (dce ss) := by
        simp [validateAux, hdead]
      rw [hdce, hva]; exact ih
    | false =>
      have hdce : dce (i :: ss) = i :: dce ss := by simp [dce, hdead]
      have hva : validateAux (i :: ss) (i :: dce ss) = validateAux ss (dce ss) := by
        simp [validateAux, hdead]
      rw [hdce, hva]; exact ih

/-- **Corollary: DCE is semantics-preserving.** Combining soundness with
    non-vacuity gives an unconditional guarantee for the modelled pass. -/
theorem dce_sound (p : Mir) : ∀ env, evalResult p env = evalResult (dce p) env :=
  validate_sound p (dce p) (dce_validates p)

/-! ## 8. Adversarial counter-example (plan §(b) acceptance criterion 3)

    Removing a LIVE instruction must be REJECTED, and doing so genuinely changes the
    observable result — so the validator is discriminating, not accept-everything.

    Source (resultReg = 0):  r1 := 5 ;  r0 := r1     (result r0 = 5).
    The first instruction is LIVE (r1 is read by the copy). -/

def advSrc : Mir := [Instr.const 1 5, Instr.copy 0 1]

/-- Bad target: the LIVE `const 1 5` has been (unsoundly) deleted. -/
def advBadTgt : Mir := [Instr.copy 0 1]

/-- The validator REJECTS removal of the live instruction. -/
theorem adv_rejected : validate advSrc advBadTgt = false := by decide

/-- …and rejection is warranted: the two programs genuinely disagree on the result
    register (5 vs the uninitialised value 0 from the all-zero input). -/
theorem adv_result_differ :
    evalResult advSrc (fun _ => 0) ≠ evalResult advBadTgt (fun _ => 0) := by decide

/-- `advSrc` has nothing dead, so DCE leaves it unchanged (and it validates). -/
theorem dce_advSrc : dce advSrc = advSrc := by decide
theorem adv_src_validates : validate advSrc (dce advSrc) = true := by decide

/-! ## 9. Positive dead-store example (the pass actually removes something)

    Source:  r5 := 99 ;  r0 := 7.  Register 5 is never read and is not the result,
    so `r5 := 99` is a DEAD STORE.  DCE removes it; the result (r0 = 7) is
    unchanged, and the deletion is a genuine rewrite. -/

def deadSrc : Mir := [Instr.const 5 99, Instr.const 0 7]

/-- DCE removes the dead store, leaving just the result-defining instruction. -/
theorem dce_deadSrc : dce deadSrc = [Instr.const 0 7] := by decide

/-- The removal is a REAL rewrite (target differs from source). -/
theorem deadSrc_is_real_rewrite : deadSrc ≠ dce deadSrc := by decide

/-- The validator accepts the dead-store elimination. -/
theorem deadSrc_validates : validate deadSrc (dce deadSrc) = true := by decide

/-- …and it is semantics-preserving on the observable result (both give r0 = 7). -/
theorem deadSrc_result_same :
    evalResult deadSrc (fun _ => 0) = evalResult (dce deadSrc) (fun _ => 0) := by decide

/-! ## 10. Overflow-faithfulness spot check

    The value model wraps at 64 bits, so a dead store of an overflowing constant is
    still handled by exact 64-bit words (no unbounded-Int cheat lurking). -/

def maxU64 : Val := 0xFFFFFFFFFFFFFFFF

theorem wrap_overflow : maxU64 + 1 = 0 := by decide

/-! Compile-time demonstrations (evaluate in the kernel, no axioms). -/
#eval (maxU64 + 1 : Val)                          -- 0x0000000000000000#64
#eval evalResult advSrc (fun _ => 0)              -- 0x0000000000000005#64
#eval evalResult advBadTgt (fun _ => 0)           -- 0x0000000000000000#64
#eval evalResult deadSrc (fun _ => 0)             -- 0x0000000000000007#64

/-! ## 11. Disclosed axiom footprint -/

#print axioms validate_sound
#print axioms dce_validates
#print axioms adv_rejected

end MirDceTv
