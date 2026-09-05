/-
  MirComposeTv — DO-333 PASS-COMPOSITION meta-theorem for translation validation.

  This is the *framework capstone* of the per-pass MIR translation-validation
  tree (`mir_opt_tv`, `mir_dce_tv`, …). Each sibling project proves that ONE
  concrete optimization pass is validated soundly. This project proves the
  glue that makes those per-pass results COMPOSE into a whole-pipeline
  soundness guarantee: if every pass in a pipeline is a "sound pass", then the
  full pipeline preserves the program's meaning end-to-end.

  ── The abstract pass interface ────────────────────────────────────────────
  A `Pass` is an OPAQUE pair of
    * `run      : Mir → Mir`      — the transformation the compiler applies, and
    * `validate : Mir → Mir → Bool` — the per-compile checker it runs afterward.
  A pass is `SoundPass` when
    (1) it always emits validator-accepted output   (`validate p (run p) = true`), and
    (2) its validator is semantics-preserving        (`validate a b = true → eval a = eval b`).
  From (1)+(2) a sound pass preserves semantics on its own output
  (`SoundPass.preserves`). Nothing below inspects the INTERNALS of `run` or
  `validate` — the composition theorems are entirely validator-agnostic, so
  they apply verbatim to the richer lockstep validators proved sound in the
  sibling projects.

  ── What is proved ─────────────────────────────────────────────────────────
    * `comp_sound`        : sequential composition of two sound passes is a sound pass.
    * `seq_compose_sound` : …stated directly on `eval` (pass1 then pass2 preserves meaning).
    * `pipeline_sound`    : a LIST of sound passes, folded, preserves meaning end-to-end.
    * `composeAll_sound`  : that same fold collapsed back into a single sound `Pass`.
    * Two concrete non-vacuous instances (`passSelfCopyElim`, `passAddComm`),
      each proved `SoundPass`, and shown to genuinely transform code.
    * Adversarial: an UNSOUND pass (`passBad`) is proved NOT `SoundPass`, a
      pipeline containing it fails `AllSound`, AND its end-to-end conclusion is
      false — so the `AllSound` hypothesis of `pipeline_sound` is genuinely
      required (it cannot be dropped).

  ── Value model ────────────────────────────────────────────────────────────
  Values are faithful 64-bit machine words (`BitVec 64`); `+` wraps modulo 2^64
  exactly like the backend's `add`. This matches the sibling projects, so the
  soundness notion composed here is the same overflow-faithful one they prove.

  ── Honesty / scope (see honest_scope) ─────────────────────────────────────
  The `Pass` abstraction is the load-bearing modelling choice. It captures a
  compiler pass as (transformation + post-hoc Boolean validator), which is
  exactly the translation-validation shape. The two CONCRETE instances here use
  a deterministic recompute-and-compare validator (`validate a b := b = run a`)
  to keep their soundness proofs short; the *interesting* non-recompute lockstep
  validators live in `mir_opt_tv`. Because the composition theorems only consume
  the two `SoundPass` conditions, plugging a sibling's real pass into this
  framework requires no change here. Straight-line `Mir` only (no CFG/loops at
  the pipeline layer — control flow is handled inside `mir_opt_tv`).

  All theorems use the Lean core library only (no Mathlib) and no proof-trust
  bypasses: no unproved placeholders, no `native_decide`, no added axioms.
  The repo `check-lean-proofs.shs` TRUST_RE gate must find nothing.
-/
namespace MirComposeTv

/-! ## 1. Syntax and semantics of the straight-line MIR fragment -/

/-- A virtual register is identified by a natural number. -/
abbrev Reg : Type := Nat

/-- Machine values are 64-bit words; `+` wraps modulo 2^64 like the backend. -/
abbrev Val : Type := BitVec 64

/-- Straight-line MIR instructions. -/
inductive Instr where
  | const : Reg → Val → Instr
  | add   : Reg → Reg → Reg → Instr
  | copy  : Reg → Reg → Instr
  deriving DecidableEq

/-- A MIR fragment is a straight-line list of instructions. -/
abbrev Mir : Type := List Instr

/-- A register file maps every register to its current value. -/
abbrev Env : Type := Reg → Val

/-- Point update of a register file. -/
def upd (env : Env) (r : Reg) (v : Val) : Env :=
  fun x => if x = r then v else env x

/-- Updating a register to its own current value is a no-op. -/
theorem upd_self (env : Env) (r : Reg) : upd env r (env r) = env := by
  funext x
  show (if x = r then env r else env x) = env x
  split
  · next h => subst h; rfl
  · rfl

/-- One-step concrete execution of a single instruction. -/
def evalInstr (env : Env) (i : Instr) : Env :=
  match i with
  | .const d v => upd env d v
  | .add d a b => upd env d (env a + env b)
  | .copy d s  => upd env d (env s)

/-- Whole-fragment semantics: fold the per-instruction step left-to-right. -/
def eval (p : Mir) (env : Env) : Env := p.foldl evalInstr env

@[simp] theorem eval_nil (env : Env) : eval [] env = env := rfl

theorem eval_cons (i : Instr) (is : Mir) (env : Env) :
    eval (i :: is) env = eval is (evalInstr env i) := rfl

/-! ## 2. The abstract pass interface -/

/-- A compiler pass: a transformation plus its post-hoc translation validator. -/
structure Pass where
  run      : Mir → Mir
  validate : Mir → Mir → Bool

/-- A pass is SOUND when it always emits validator-accepted output AND its
    validator only ever accepts semantics-preserving rewrites. -/
def SoundPass (P : Pass) : Prop :=
  (∀ p, P.validate p (P.run p) = true) ∧
  (∀ a b, P.validate a b = true → ∀ env, eval a env = eval b env)

/-- A sound pass preserves semantics on its own output. -/
theorem SoundPass.preserves {P : Pass} (h : SoundPass P) (p : Mir) :
    ∀ env, eval p env = eval (P.run p) env :=
  h.2 p (P.run p) (h.1 p)

/-! ## 3. Sequential composition of two passes -/

/-- Run `P` then `Q`. The composed validator re-checks `P`'s step on the
    intermediate it recomputes, then `Q`'s step to the final target. -/
def comp (P Q : Pass) : Pass where
  run      := fun p => Q.run (P.run p)
  validate := fun a c => P.validate a (P.run a) && Q.validate (P.run a) c

/-- **Sequential composition preserves soundness.** The composite of two sound
    passes is itself a sound pass. -/
theorem comp_sound {P Q : Pass} (hP : SoundPass P) (hQ : SoundPass Q) :
    SoundPass (comp P Q) := by
  constructor
  · -- always emits validator-accepted output
    intro p
    simp only [comp, hP.1 p, hQ.1 (P.run p), Bool.and_self]
  · -- the composed validator is semantics-preserving
    intro a c hac env
    simp only [comp, Bool.and_eq_true] at hac
    obtain ⟨h1, h2⟩ := hac
    have e1 : eval a env = eval (P.run a) env := hP.2 a (P.run a) h1 env
    have e2 : eval (P.run a) env = eval c env := hQ.2 (P.run a) c h2 env
    rw [e1, e2]

/-- **Direct `eval`-level statement:** running two sound passes in sequence
    preserves the meaning of every fragment. -/
theorem seq_compose_sound {P Q : Pass} (hP : SoundPass P) (hQ : SoundPass Q)
    (p : Mir) : ∀ env, eval p env = eval (Q.run (P.run p)) env :=
  (comp_sound hP hQ).preserves p

/-! ## 4. Pipelines: a list of passes, folded -/

/-- Run a whole pipeline left-to-right. -/
def runPipeline (ps : List Pass) (p : Mir) : Mir :=
  ps.foldl (fun m P => P.run m) p

/-- Every pass in the list is sound. -/
def AllSound (ps : List Pass) : Prop := ∀ P ∈ ps, SoundPass P

/-- **Main pipeline meta-theorem.** A pipeline of sound passes preserves the
    meaning of every fragment end-to-end. -/
theorem pipeline_sound (ps : List Pass) (h : AllSound ps) :
    ∀ p env, eval p env = eval (runPipeline ps p) env := by
  induction ps with
  | nil => intro p env; rfl
  | cons P rest ih =>
    intro p env
    have hP : SoundPass P := h P (by simp)
    have hrest : AllSound rest := fun Q hQ => h Q (by simp [hQ])
    -- runPipeline (P :: rest) p  ≡  runPipeline rest (P.run p)
    show eval p env = eval (runPipeline rest (P.run p)) env
    rw [hP.preserves p env]
    exact ih hrest (P.run p) env

/-! ## 5. Collapsing a pipeline back into a single sound `Pass` -/

/-- The identity pass: no transformation, and its validator accepts exactly the
    unchanged program. Trivially sound. -/
def idPass : Pass where
  run      := id
  validate := fun a b => decide (a = b)

theorem idPass_sound : SoundPass idPass := by
  constructor
  · intro p; simp [idPass]
  · intro a b hab env
    simp only [idPass, decide_eq_true_eq] at hab
    subst hab; rfl

/-- Fold a whole pipeline into one `Pass` by iterated `comp`. -/
def composeAll (ps : List Pass) : Pass := ps.foldl comp idPass

/-- Folding `comp` from a sound accumulator over sound passes stays sound. -/
theorem foldl_comp_sound (ps : List Pass) :
    ∀ acc, SoundPass acc → AllSound ps → SoundPass (ps.foldl comp acc) := by
  induction ps with
  | nil => intro acc hacc _; exact hacc
  | cons P rest ih =>
    intro acc hacc h
    have hP : SoundPass P := h P (by simp)
    have hrest : AllSound rest := fun Q hQ => h Q (by simp [hQ])
    exact ih (comp acc P) (comp_sound hacc hP) hrest

/-- **Pass-level capstone.** The `comp`-fold of a list of sound passes is a
    single sound `Pass`. -/
theorem composeAll_sound (ps : List Pass) (h : AllSound ps) :
    SoundPass (composeAll ps) :=
  foldl_comp_sound ps idPass idPass_sound h

/-! ## 6. Concrete pass #1 — self-copy (no-op) elimination -/

/-- `copy d d` writes a register's own value back to itself: a semantic no-op. -/
def isSelfCopy : Instr → Bool
  | .copy d s => decide (d = s)
  | _         => false

/-- Executing a self-copy leaves the register file unchanged. -/
theorem evalInstr_selfCopy (env : Env) (i : Instr) (h : isSelfCopy i = true) :
    evalInstr env i = env := by
  cases i with
  | const d v => simp [isSelfCopy] at h
  | add d a b => simp [isSelfCopy] at h
  | copy d s =>
    simp only [isSelfCopy, decide_eq_true_eq] at h
    show upd env d (env s) = env
    rw [h]; exact upd_self env s

/-- Drop every `copy d d`. -/
def selfCopyElimRun : Mir → Mir
  | []      => []
  | i :: is =>
    match isSelfCopy i with
    | true  => selfCopyElimRun is
    | false => i :: selfCopyElimRun is

theorem selfCopyElim_preserves :
    ∀ (p : Mir) (env : Env), eval p env = eval (selfCopyElimRun p) env := by
  intro p
  induction p with
  | nil => intro env; rfl
  | cons i is ih =>
    intro env
    cases h : isSelfCopy i with
    | true =>
      rw [eval_cons, evalInstr_selfCopy env i h]
      simp only [selfCopyElimRun, h]
      exact ih env
    | false =>
      rw [eval_cons]
      simp only [selfCopyElimRun, h]
      rw [eval_cons]
      exact ih (evalInstr env i)

/-! ## 7. Concrete pass #2 — add-operand canonicalization (commutativity) -/

/-- Rewrite `add d a b` to `add d b a`; leave everything else alone. -/
def addCommInstr : Instr → Instr
  | .add d a b => .add d b a
  | i          => i

/-- Swapping the operands of a wrapping 64-bit `add` preserves its effect. -/
theorem evalInstr_addComm (env : Env) (i : Instr) :
    evalInstr env (addCommInstr i) = evalInstr env i := by
  cases i with
  | const d v => rfl
  | copy d s  => rfl
  | add d a b =>
    show upd env d (env b + env a) = upd env d (env a + env b)
    rw [BitVec.add_comm]

/-- Canonicalize every `add` in the fragment. -/
def addCommRun (p : Mir) : Mir := p.map addCommInstr

theorem addComm_preserves :
    ∀ (p : Mir) (env : Env), eval p env = eval (addCommRun p) env := by
  intro p
  induction p with
  | nil => intro env; rfl
  | cons i is ih =>
    intro env
    rw [eval_cons]
    show eval is (evalInstr env i) = eval (addCommRun (i :: is)) env
    simp only [addCommRun, List.map_cons]
    rw [eval_cons, evalInstr_addComm]
    exact ih (evalInstr env i)

/-! ## 8. Both concrete passes are sound instances of the interface -/

/-- Build a deterministic pass whose validator recomputes `run` and compares:
    a legitimate (if degenerate) translation validator for a deterministic pass.
    Soundness then reduces entirely to `run` preserving semantics. -/
def mkDetPass (run : Mir → Mir) : Pass where
  run      := run
  validate := fun a b => decide (b = run a)

theorem mkDetPass_sound (run : Mir → Mir)
    (hpres : ∀ a env, eval a env = eval (run a) env) :
    SoundPass (mkDetPass run) := by
  constructor
  · intro p; simp [mkDetPass]
  · intro a b hab env
    simp only [mkDetPass, decide_eq_true_eq] at hab
    subst hab
    exact hpres a env

def passSelfCopyElim : Pass := mkDetPass selfCopyElimRun
def passAddComm      : Pass := mkDetPass addCommRun

theorem passSelfCopyElim_sound : SoundPass passSelfCopyElim :=
  mkDetPass_sound _ selfCopyElim_preserves

theorem passAddComm_sound : SoundPass passAddComm :=
  mkDetPass_sound _ addComm_preserves

/-- Non-vacuity: the passes genuinely transform code (they are not the identity). -/
theorem passAddComm_transforms :
    passAddComm.run [Instr.add 0 1 2] = [Instr.add 0 2 1] := by decide

theorem passSelfCopyElim_transforms :
    passSelfCopyElim.run [Instr.copy 0 0, Instr.const 1 5] = [Instr.const 1 5] := by
  decide

/-! ## 9. A concrete SOUND pipeline (framework is non-vacuous end-to-end) -/

def goodPipeline : List Pass := [passAddComm, passSelfCopyElim]

theorem goodPipeline_allSound : AllSound goodPipeline := by
  intro P hP
  simp only [goodPipeline, List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with h | h <;> subst h
  · exact passAddComm_sound
  · exact passSelfCopyElim_sound

/-- End-to-end soundness of a real two-pass pipeline, via `pipeline_sound`. -/
theorem goodPipeline_sound :
    ∀ p env, eval p env = eval (runPipeline goodPipeline p) env :=
  pipeline_sound goodPipeline goodPipeline_allSound

/-- …and its collapsed single-`Pass` form is sound too. -/
theorem goodPipeline_composeAll_sound : SoundPass (composeAll goodPipeline) :=
  composeAll_sound goodPipeline goodPipeline_allSound

/-! ## 10. Adversarial: one unsound step breaks the end-to-end guarantee

    `passBad` clobbers every program to `[const 0 99]`, discarding its input.
    Its recompute validator still accepts its own output (condition (1) holds),
    but condition (2) FAILS — the validator accepts a semantics-changing
    rewrite. We prove it is NOT a sound pass, that a pipeline containing it
    fails `AllSound`, and that this same pipeline's end-to-end conclusion is
    false. Together these show the `AllSound` hypothesis of `pipeline_sound`
    is genuinely load-bearing: drop it and the theorem is false. -/

def badRun (_ : Mir) : Mir := [Instr.const 0 99]
def passBad : Pass := mkDetPass badRun

/-- The bad validator accepts `[] ↦ [const 0 99]`, yet the two disagree at
    register 0 (0 vs 99): a witnessed violation of validator soundness. -/
theorem passBad_validator_unsound :
    passBad.validate [] (badRun []) = true ∧
      (eval [] (fun _ => 0)) 0 ≠ (eval (badRun []) (fun _ => 0)) 0 := by
  refine ⟨by decide, by decide⟩

/-- **`passBad` is not a sound pass.** -/
theorem passBad_not_sound : ¬ SoundPass passBad := by
  intro h
  have heq := h.2 [] (badRun []) (h.1 []) (fun _ => 0)
  exact passBad_validator_unsound.2 (congrFun heq 0)

def badPipeline : List Pass := [passSelfCopyElim, passBad]

/-- A pipeline containing the unsound pass fails the `AllSound` hypothesis. -/
theorem badPipeline_not_allSound : ¬ AllSound badPipeline := by
  intro h
  exact passBad_not_sound (h passBad (by simp [badPipeline]))

theorem badPipeline_result : runPipeline badPipeline [] = [Instr.const 0 99] := rfl

/-- **The conclusion genuinely fails** for the bad pipeline: the original `[]`
    and the pipeline's output disagree at register 0 (0 vs 99). Hence the
    `AllSound` hypothesis of `pipeline_sound` cannot be dropped. -/
theorem badPipeline_breaks :
    (eval [] (fun _ => 0)) 0 ≠ (eval (runPipeline badPipeline []) (fun _ => 0)) 0 := by
  rw [badPipeline_result]; decide

/-- The two adversarial facts, side by side: the hypothesis is necessary. -/
theorem allSound_hypothesis_necessary :
    ¬ AllSound badPipeline ∧
      (eval [] (fun _ => 0)) 0 ≠ (eval (runPipeline badPipeline []) (fun _ => 0)) 0 :=
  ⟨badPipeline_not_allSound, badPipeline_breaks⟩

/-! ## 11. Disclosed axiom footprint -/

#print axioms comp_sound
#print axioms seq_compose_sound
#print axioms pipeline_sound
#print axioms composeAll_sound
#print axioms passBad_not_sound
#print axioms allSound_hypothesis_necessary

end MirComposeTv
