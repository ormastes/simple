# Tool Qualification Plan — the Simple Compiler (DO-330 / ISO 26262-8 §11)

Cert Phase 7 / deferred task **C7** (`cert_roadmap.md`, `deferred_tasks_plan.md`). Target
grade: aero-a/auto-d requires this; nearest-achievable aero-d/auto-a does not, but the
plan is executable **now** on the clean `bin/simple` — the stage4 wall is
seed-cranelift-only and out of scope here per `cert_roadmap.md` § Root ordering constraint
(CORRECTED 2026-07-05). Companion to `psac.md`/`svp.md`.

The compiler translates requirements-based source into the executable/loadable image;
its output is not independently verified instruction-by-instruction, so a compiler defect
could introduce an error into airborne software → it is a **development tool** whose
output must be qualified (DO-330). This is the most detailed plan in the cert set.

---

## 1. Tool Operational Requirements (TOR)

### 1.1 Tool identity and use-context

- **Tool:** the pure-Simple self-hosted compiler, deployed as
  `bin/release/<triple>/simple` (`bin/simple` symlink). **Not** the Rust seed
  (`src/compiler_rust`), which is bootstrap-only and explicitly excluded (see KP-001).
- **DO-330 qualification criterion:** the compiler can *insert an error* into the product
  (it generates code) → **Criterion 1** (the most stringent), TQL-1 at DAL A. It is not
  merely a Criterion-2/3 tool whose failure only fails-to-detect. This plan is written to
  Criterion 1.
- **Use context:** translate `.spl` source (`src/compiler`, `src/lib`, `src/app`, plus
  application source) → executable, via the pure-Simple frontend + `70.backend` codegen,
  on the pinned Tool Operational Environment (see §3.2).

### 1.2 Required tool functions (each must have corpus + failure-mode coverage)

| Fn | Requirement |
|---|---|
| TOR-F1 Lex/Parse | accept every valid construct in the language grammar; reject malformed input with a diagnostic |
| TOR-F2 Type-check | accept well-typed programs; reject ill-typed with a diagnostic; no unsound acceptance |
| TOR-F3 Lower/Optimize | HIR→MIR→codegen preserves source semantics across opt levels |
| TOR-F4 Codegen | emitted code computes the source-specified result on the target ISA |
| TOR-F5 Determinism | identical (source, TOE) → byte-identical output (already Phase-5 proven) |
| TOR-F6 Diagnostics | rejects are truthful (point at a real defect), not spurious |
| TOR-F7 Coverage instrumentation | when `SIMPLE_COVERAGE` is set, reported coverage is neither over- nor under-counted (depends on C1) |

### 1.3 Tool failure-mode table

Each failure mode has a detecting guard/mitigation. A qualified release requires every
row GREEN (or a live waiver in the known-problem list, §3).

| Id | Failure mode | Consequence | Detecting mitigation |
|---|---|---|---|
| TOR-FM-01 | Miscompilation (correct-looking code, wrong result) | latent product defect | validation corpus `positive/` golden-`.expected` diff (§2); optimization-soundness differential C2 (interp vs cranelift-O0/O2) |
| TOR-FM-02 | Silent accept of a bad program (unsound type-check / missing reject) | ill-typed code ships | `negative/` corpus: each must be REJECTED with the expected diagnostic |
| TOR-FM-03 | Silent reject of a good program | valid code blocked / workaround introduced | `positive/` corpus: each must COMPILE and run to its golden output |
| TOR-FM-04 | Nondeterminism | non-reproducible build; CM baseline unverifiable | TOR-F5 build-twice sha256 gate (`cert_roadmap.md` Phase 5) |
| TOR-FM-05 | Optimizer divergence (O0 vs O2 differ) | opt-dependent latent defect | C2 soundness differential across opt levels; `meta/` corpus asserts opt-invariance |
| TOR-FM-06 | Coverage under-report (probe drops a condition) | false MC/DC confidence | `meta/` corpus with known condition counts vs reported (depends on C1); until C1, coverage is statement-only and labeled as such |
| TOR-FM-07 | Known-problem regression (a fixed defect returns) | silent re-breakage | `known_problem/` corpus: each fixed defect keeps a permanent regression test with its golden output |

---

## 2. Qualified validation corpus

### 2.1 Layout — `test/cert/tool_qual/` (new)

GCC-torture / ACATS-style corpus, one directory per category, mirroring every
language-construct family:

```
test/cert/tool_qual/
  positive/        # valid programs that MUST compile+run to golden output
    arithmetic/ structs/ enums/ matches/ generics/ closures/ traits/
    mixins/ modules/ actors/ async/ ffi/ memory_tiers/ ...   (one per construct family)
  negative/        # invalid programs that MUST be rejected with the expected diagnostic
    type_errors/ borrow_errors/ visibility_errors/ arity_errors/ syntax_errors/ ...
  known_problem/   # permanent regression test per previously-fixed compiler defect
                   # (e.g. the 938a4eb Result/Option payload-index defect, the #103/#107/#117
                   #  ANY-erased enum-channel class) — named by the fixing commit
  meta/            # tool-property tests: determinism, opt-invariance (O0==O2 output),
                   # coverage-count-vs-reported, diagnostic-truthfulness
  <category>/<case>.spl
  <category>/<case>.expected     # golden: stdout|exit-code|diagnostic-substring, per case
```

Every construct family in the language reference must have ≥1 `positive/` case; every
diagnostic code emitted by the frontend must have ≥1 `negative/` case that provokes it.

### 2.2 Oracle-independence policy

The corpus's authority is its **golden `.expected` files**, authored/reviewed
**independently of the compiler under test** — the expected result comes from the
language specification / hand computation / a reference interpreter run that is itself
corpus-frozen, never from "whatever the current compiler prints." This is the independent
oracle the bootstrap fixpoint lacks (§4). For `positive/` cases the expected value is the
mathematically/spec-determined result; for `negative/`, the expected diagnostic
substring; the compiler is never permitted to define its own pass criterion.

### 2.3 Golden immutability + freeze tool

- `.expected` files are checked into git and **immutability-gated**: a pre-commit check
  (extend `scripts/hooks/pre-commit`) rejects any edit to an existing
  `test/cert/tool_qual/**/*.expected` unless the commit message carries an explicit
  `TOOLQUAL-REBASELINE: <reason>` token — golden outputs cannot drift silently to match a
  regressed compiler.
- **Freeze tool** `scripts/check/cert/freeze-tool-qual-golden.shs` (new): for a *new*
  case with no `.expected` yet, records the independently-derived expected output into the
  golden file (never overwrites an existing one). Adding goldens is a deliberate,
  reviewed act; regenerating them wholesale is impossible by construction.

### 2.4 Runner — `scripts/check/cert/run-tool-qual-corpus.shs` (new)

- Walks `test/cert/tool_qual/`, compiles+runs each `positive/`/`known_problem/`/`meta/`
  case with `bin/simple`, diffs against `.expected`; asserts each `negative/` case is
  rejected with the expected diagnostic substring; prints a per-category PASS/FAIL table
  and exits nonzero on any mismatch (same exit-code/`--self-test` convention as
  `check-lean-proofs.shs` / `check-req-traceability.shs`).
- **Wired into `bin/simple build check`** (so the corpus runs on every quality gate) and
  **required GREEN before release tagging** (`scmp.md` § Baseline/release identification).

---

## 3. Known-problem list + Tool Operational Environment

### 3.1 Known-problem list — `doc/08_tracking/cert/tool_known_problems.{md,sdn}` (new)

- Bidirectionally linked like the traceability checker: each `KP-NNN` in the `.md` links
  to the `known_problem/` corpus case pinning it, and each `known_problem/` case cites its
  `KP-NNN`; a checker (extend `check-req-traceability.shs`'s pattern) flags a KP with no
  pinning test (orphan-down) or a `known_problem/` case citing an unknown KP (orphan-up).
- `.sdn` is the machine-readable ledger (id, title, status open|fixed|waived, fixing
  commit, pinning corpus case, date). A qualified release ships with 0 open KPs affecting
  a required function, or each is waived with justification + expiry.

### 3.2 Tool Operational Environment (TOE) pin — `doc/08_tracking/cert/tool_operational_environment.md` (new)

Records the exact qualified configuration: the `bin/release/<triple>/simple` binary
sha256, the source commit id it was built from, the enabled backends (cranelift/llvm/
interp) and target triples, and the host/toolchain. **Explicitly records the seed-built
stage4 as KP-001 (excluded/not-qualified):** the 144 MB Rust seed's cranelift mis-lowers
the ANY-erased `Dict<text,Value>`/enum-payload channel (`redeploy_selfhost_plan.md`); the
qualified tool is the pure-Simple `bin/simple` codegen, and any seed-built stage4 is
out of the qualified TOE by construction.

---

## 4. Why the bootstrap fixpoint is not qualification evidence

The 3-stage bootstrap produces stage2==stage3 (byte-identical). This proves **self-
consistency**: the compiler compiles itself to a fixed point. It does **not** prove
**correctness**. A *systematic, self-consistent* miscompilation — a defect present in
stage2 that the stage2 compiler reproduces identically when building stage3 — survives the
fixpoint unchanged and is invisible to the stage2==stage3 check. The fixpoint compares the
compiler against *itself*; it has no independent notion of the *correct* output.

The validation corpus (§2) supplies exactly the missing piece: an **independent oracle**
(spec-derived golden outputs, §2.2) against which the tool's output is judged — the
evidence DO-330 requires and the fixpoint cannot provide. Fixpoint = necessary sanity
check; corpus = the qualification evidence.

---

## 5. Execution order (7 steps, runnable now on clean `bin/simple`)

1. **Scaffold** `test/cert/tool_qual/{positive,negative,known_problem,meta}/` +
   `scripts/check/cert/{run-tool-qual-corpus.shs,freeze-tool-qual-golden.shs}` with
   `--self-test` modes (plant a known pass + a known fail, assert classification).
2. **Seed `known_problem/`** from already-fixed defects (938a4eb Result/Option payload
   index; the #103/#107/#117 ANY-enum-channel class; each with its independently-derived
   golden), and create `doc/08_tracking/cert/tool_known_problems.{md,sdn}` (KP-001 = seed
   stage4 excluded) + the TOE pin doc.
3. **Populate `positive/`** one construct family at a time (arithmetic→structs→enums→
   matches→generics→closures→traits→mixins→modules→actors→async→ffi→memory-tiers),
   freezing each golden via the freeze tool with a spec/hand-computed expected value.
4. **Populate `negative/`** to cover every emitted diagnostic code (one provoking case
   each), expected = diagnostic substring.
5. **Populate `meta/`**: determinism (build-twice sha256), opt-invariance (O0==O2 output),
   diagnostic-truthfulness; add coverage-count meta cases once C1 lands.
6. **Wire the runner** into `bin/simple build check` and make it a required gate before
   release tagging (`scmp.md`); add the golden-immutability check to the pre-commit hook.
7. **Author the Tool Qualification Data**: this plan + a Tool Accomplishment Summary
   (corpus results per release) + the TOR/known-problem docs = the DO-330 data package;
   re-run the corpus every release and append results to `cert_roadmap.md`.

**Acceptance for C7:** corpus GREEN every release; every required tool function (TOR-F1..
F7) and every failure mode (TOR-FM-01..07) covered by ≥1 corpus case or a live waiver;
TOR + known-problem-list + TOE pin maintained; independent-oracle policy upheld (no golden
derived from the tool under test).
