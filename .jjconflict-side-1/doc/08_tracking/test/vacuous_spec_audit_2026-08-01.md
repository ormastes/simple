# Vacuous-spec audit, 2026-08-01 (redo)

Lane: vacuous-spec audit, run in an isolated tmpfs worktree extracted with
`git archive` from origin/main. The shared working copy was never modified.

Every claim below is marked **PROVED** (transcript reproduced here) or
**INFERRED** (extrapolated from a measured sample).

Base tip for the census: `55115a82411a596449060679a8c837cc63c48c01`,
tree 109,542 files. Counts re-checked stable at `d318ad62d59` (109,552 files) --
the small drift is unrelated files landing from parallel lanes.

---

## 0. Corrections to numbers handed to this lane

### The "~303 suspected vacuous" figure is REPRODUCED, and it is an overstatement

**PROVED.** The candidate pool at this tip is **302**, not 303 -- see the census
table. The one-file gap is drift between tips, not a methodology difference.

But 302 is the *candidate* count. Hand-verification (section 3) shows only
about **62% of it is genuinely vacuous**; the remaining 38% is a different
defect (specs that are already RED). Reporting 303 as "vacuous" overstates by
roughly 114 files.

### The prior lane's "decisive proof" was invalid, and so was this lane's first census

Two separate measurement failures are recorded here because both are the same
mistake in different clothes -- measuring a proxy and reporting it as the thing.

1. **The `di.spl` sabotage.** `src/compiler/di.spl` is a 19-line forwarding
   module; the spec exercises `compiler/00.common/di.spl` directly. Gutting the
   shim removed nothing the spec depended on. The spec passing was correct.

2. **This lane's own first pass.** The v1 detector matched only `expect(` and
   reported **1,161 NOASSERT** files. It was wrong: this repo uses *two*
   assertion spellings, and the parenthesis-free prefix form is the common one:

       expect f.render_pass_list.len() to_equal 0      # prefix form  (missed)
       expect(x).to_equal(y)                            # call form    (matched)

   Correcting the detector dropped NOASSERT from 1,161 to **247**. `1,161` was
   inflated ~4.7x. Any number derived from the v1 scan must be discarded.

   The file that exposed this -- `test/01_unit/lib/viz/compositor_frame_spec.spl`
   -- was v1-classified NOASSERT and is in fact a fully gating spec; see 2.1.

---

## 1. Census (PROVED)

Scope: `test/**/*_spec.spl` = **16,975** files. (171 further `*_spec.spl` live
outside `test/` and are excluded.)

| Class | Files | Meaning |
|---|---:|---|
| OK | 15,963 | at least one assertion that can fail |
| PLACEHOLDER | 710 | every assertion is a `pending_reason` fake-green |
| NOASSERT_LIVE | 173 | declares `it`/`describe`, contains **zero** assertions |
| NOASSERT_INERT | 74 | no assertions **and** no `it`/`describe` |
| TRIVIAL_LIT | 55 | every assertion is on a literal (`expect(true).to_equal(true)`) |
| **total** | **16,975** | |

**Candidate pool = 173 + 74 + 55 = 302.** This is the "~303".

The 173 NOASSERT_LIVE files declare **1,816 `it` blocks**, none of which can
fail. Of those, **36 files / 1,099 blocks** have a body that is the bare
statement `pass`.

PLACEHOLDER is counted separately because it is the already-documented
`pending_reason` family (`doc/08_tracking/bug/vacuous_spec_census_2026-07-30.md`).
Note that census reported 1,154 files containing `pending_reason`; at this tip
the measured figure is **728**. The older number is not reproducible here.

---

## 2. The decisive test, done correctly

The test is "break the subject and watch it go RED" -- targeting the
implementation the spec's import path actually resolves to, and corrupting a
**specific symbol's return value** rather than deleting a file.

Harness validated first, because an unvalidated harness is how the last three
of these audits went wrong:

    ctrl_pass_spec.spl (expect 1 to_equal 1)  ->  rc=0  Results: 1 total, 1 passed, 0 failed
    ctrl_fail_spec.spl (expect 1 to_equal 2)  ->  rc=1  Results: 1 total, 0 passed, 1 failed

### 2.1 Negative control: a spec that DOES gate (PROVED)

Spec `test/01_unit/lib/viz/compositor_frame_spec.spl` imports
`std.viz.entity.compositor_frame`. That path resolves to
`src/lib/viz/entity/compositor_frame.spl` -- 47 lines, defines the class body
directly, **not** a forwarding module (checked by reading its head).

Two specific symbol bodies were corrupted in place:

    me root_render_pass_id() -> i32:
        return 424242            # injected
    me total_quad_count() -> i32:
        return 999999            # injected

Result:

    baseline    rc=0  Results: 9 total, 9 passed, 0 failed
    sabotaged   rc=1  Results: 9 total, 5 passed, 4 failed

The spec gates. The file was restored (`cmp` verified byte-identical).

### 2.2 A spec that does NOT gate (PROVED)

`test/unit/compiler/codegen/static_method_spec.spl` and its `test/01_unit`
mirror (identical blob `2462b312f`). 338 lines, 17 `it` blocks, **zero**
assertion tokens. Every body built a source string and then evaluated `0`:

    it "compiles static method with parameters":
        val code = """ ... """
        # Should return 15 (5 * 3)
        0

Run of the original:

    rc=0  Results: 17 total, 17 passed, 0 failed

Seventeen green cases testing nothing. Fixed -- see section 5.

### 2.3 The purest shape (PROVED)

`test/01_unit/app/interpreter/ast_convert_expr_spec.spl` -- 389 lines, 61 `it`
blocks whose entire body is the keyword `pass`:

    it "converts integer literals":
        # Test that integer nodes are recognized
        pass

    rc=0  Results: 61 total, 61 passed, 0 failed

It does not import its stated subject (`src/app/interpreter/ast_convert_expr.spl`)
at all -- the only reference is a comment. 35 further files share this shape.

---

## 3. Measured vacuity rate (PROVED sample, INFERRED population)

Stratified random sample of the 302-file candidate pool, **one spec per runner
invocation** (see section 4 for why batching is unsafe). n = 58 completed.

A file counts as *genuinely vacuous* only if it reports **green with at least
one passing case** while containing no assertion that can fail.

| Class | Population | Sampled | Green (vacuous) | Red (not vacuous) | Vacuity rate |
|---|---:|---:|---:|---:|---:|
| NOASSERT_LIVE | 173 | 30 | 25 | 5 | **83%** |
| TRIVIAL_LIT | 55 | 15 | 12 | 3 | **80%** |
| NOASSERT_INERT | 74 | 13 | 0 | 13 | **0%** |
| **pool** | **302** | **58** | **37** | **21** | **64% of sample** |

Extrapolated to the population (**INFERRED**):

    NOASSERT_LIVE   173 x 0.83  ~= 144
    TRIVIAL_LIT      55 x 0.80  ~=  44
    NOASSERT_INERT   74 x 0.00  =    0
    -----------------------------------
    genuinely vacuous            ~= 188  of 302  (62%)

### The 74 NOASSERT_INERT files are NOT vacuous -- they are already RED

**PROVED**, 13 of 13 sampled. They have no `describe`/`it`, fail to load, and
report `1 total, 0 passed, 1 failed` with a non-zero exit. Example:
`test/unit/gpu/backend_acceleration_spec.spl`. A failing spec is a visible
problem, not false confidence, so folding these into a "vacuous" headline
inflates it by 74.

This also answers audit rule 4 directly: **there is no runner fail-open on
import failure.** A spec that cannot load is reported RED with rc=1. The
fail-open in this repo is elsewhere -- see section 4.

### Sampled reds worth naming

- `test/unit/compiler/r2_probe_fail_spec.spl` and `r2_matchers_red_probe_spec.spl`
  are *intentional* RED probes. Correctly red; not defects.
- `test/unit/app/test_runner/quickcheck_spec.spl` -- `93 total, 61 passed,
  32 failed`, from 61 `pass`-bodied blocks plus 32 generated cases. Half fake
  green, half genuinely failing.

---

## 4. Separate finding: a fail-open in the runner itself

**PROVED.** `simple test a.spl b.spl` runs only the FIRST path, reports
`Files: 1`, and exits **0** -- a failing second spec is silently dropped.
Filed as `doc/08_tracking/bug/test_runner_multi_path_drops_all_but_first_2026-08-01.md`.

This is not merged into the vacuity count. It is more dangerous than any single
vacuous spec because one batched invocation can hide arbitrarily many real ones.

---

## 5. Separate category: every spec in the tree is non-gating for the compiled lanes

**PROVED**, and the number is not a subset -- it is all of them.

    $ bin/simple test --help
    error: unknown command 'test'

The deployed self-hosted `bin/simple` has no `test` subcommand at all. The only
working runner is `bin/simple_seed test`, and its own log names its engine:

    child binary: /home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple_seed

That is the Rust seed, which executes the **tree-walking interpreter**.

**Non-gating count: 16,975 / 16,975 (100%).** No spec in this repo can currently
catch a JIT-only or native-only defect, because no spec can currently be run on
those lanes. This is why the documented enum-payload and `??`-on-raw-i64 defects
are invisible to the suite: they are correct under the interpreter.

Per the audit brief these are **not** rewritten. What they need is a runner that
executes on the compiled lanes. (Note for whoever picks that up: a bare
`simple foo.spl` selects the **JIT**, not the interpreter -- a previous lane
mislabelled this and published a wrong lane table.)

---

## 6. Bugs uncovered by de-vacuum-ing (first-class findings)

Rewriting `static_method_spec.spl` to actually assert surfaced two real defects.
Per the brief these are filed, and the cases are **not** re-expressed as passing
tests.

1. **Static methods on a generic class are unresolvable.**
   `semantic: unknown static method create on class GContainer`. The identical
   shape on a non-generic class resolves fine (12 such calls pass).
   `doc/08_tracking/bug/generic_class_static_method_unresolved_2026-08-01.md`

2. **`.?` on an `i64?` returns the payload / nil instead of a bool.**
   `expected 42 to equal true`, `expected nil to equal false`.
   `doc/08_tracking/bug/exists_check_on_optional_i64_returns_payload_2026-08-01.md`

Both had a *named* `it` block in the vacuous spec -- "handles generic static
methods", "handles static method returning Option" -- that reported PASS for as
long as the file existed. The features were broken the whole time and the spec
said they worked.

---

## 7. Landed

**Batch 1** -- `f793418c80240580c0abab03f67c51bb118ab33c`:

- `test/unit/compiler/codegen/static_method_spec.spl` and its `01_unit` mirror
  rewritten. Original: `17 total, 17 passed, 0 failed`, zero assertions.
  Rewritten: `12 total, 12 passed, 0 failed`; mutating the subject (dropping a
  term from `SmCalculator.sum8`) gives `12 total, 11 passed, 1 failed`.
  RED-then-GREEN **PROVED**.
- The three bug reports above.

**Batch 2** -- this report.

---

## 8. Recommended next work, in priority order

1. **Fix the runner fail-open (section 4)** before anything else. It can hide
   any amount of the rest.
2. **Give the runner a compiled-lane mode (section 5).** Until then the whole
   suite is interpreter-only and 100% non-gating for the JIT/native defect class.
3. **The 36 `pass`-bodied files / 1,099 blocks** are the cleanest repair target
   in the vacuous pool -- one shape, mechanically identifiable, and several guard
   real subjects (`gc_safety_spec` 81 blocks, `simd_check_spec` 61,
   `macro_check_spec` 41, `const_keys_spec` 55).
4. **Triage the 74 NOASSERT_INERT reds separately.** They are broken, not
   vacuous, and need a different fix.
5. **Lint the shapes** so no new ones land: zero-assertion `it`, bare-`pass`
   body, `expect(true).to_equal(true)`, and `pending_reason`.

## 9. Reproduction

Detector must match **both** assertion spellings or every number is wrong:

    (^|[^a-zA-Z_])(expect|assert|assert_eq|assert_true|check|should_be|should_equal|must_be)([^a-zA-Z_]|$)

on non-comment lines, classifying a file by whether *all* its assertion lines
are placeholder / literal-only / self-comparing. Run one spec per invocation.
Use `/usr/bin/grep` -- the default `grep` here is ugrep and its counts differ.

The enumerated candidate list is `doc/08_tracking/test/vacuous_spec_candidates_2026-08-01.tsv`
(class, path, assertion count, trivial count, self-compare count, placeholder
count, `it` count).
