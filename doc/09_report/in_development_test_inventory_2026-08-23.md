# In-development test inventory — 2026-08-23

Lane: DATA (test/spec files). Sibling lanes own tag semantics
(`src/lib/nogc_sync_mut/spec/**`, `src/app/test_runner_new/**`) and the
statistics/`--tag` surfaces. This lane applied the tag to spec files only.

## Tag name

`@tag: in-development`, placed in the spec docstring header. This matches the
**existing** in-tree convention (`@tag: gpu, engine2d, simd`; 69 spec files
already carry a `@tag:` line) rather than inventing a new `@tag:in-development`
form. **Open coordination question for the core lane:** if the runner expects
the no-space `@tag:in-development` form used in `src/lib/.../engine_probe.spl`,
say so and this lane will re-normalize — it is a one-line change in one file.

## Method — and why the recorded DB was NOT usable

`doc/08_tracking/test/test_result.md` (2026-08-22 09:43) reports
**Total 770 / Passed 0 / Failed 0**, and `test_db.sdn` is internally
incoherent: the `tests` table carries one uniform `status_str` for all 787
rows, `counters` holds only **74** rows for 770 tests, and joining
`tests -> suites -> files` yields rows whose file and test name disagree
(e.g. file `qemu_user_integration_spec.spl` paired with name
`runtime_array_assignment_ssa_spec.spl`). **The recorded DB cannot be used to
derive a failing set** and should be treated as a separate defect.

Used instead: targeted re-runs against the deployed seed
`/mnt/data/worktrees/goal-main-1/bin/simple`, `SIMPLE_TIMEOUT_SECONDS=0`,
2 jobs, in a fresh worktree at `origin/main` `3ccf808f6f2`. Verdicts read from
the `SPEC FILE VERDICT` line (the runner's exit code is unreliable — see
`test_runner_exits_zero_on_failed_spec_2026-08-21.md`). 19 specs run: the whole
of `test/01_unit/compiler/mono/` (17), plus `semantics/union_narrowing_spec.spl`
and `driver/mono_pipeline_surfaces_unresolved_generic_spec.spl`.

Result: **18 of 19 GREEN, 1 RED.**

## Tagged (1)

| Spec | Verdict | Reason | Record |
|---|---|---|---|
| `test/01_unit/compiler/mono/free_generic_fn_two_module_native_spec.spl` | 0/4 | #158 Phase B/C cross-module free-generic-fn specialization is unfinished feature work. The spec was **born RED with the feature commit `625c245bafa`** and has never passed — verified via `git log --follow`; the later touch `8f4a6f24c0a` explicitly records it as "pre-existing RED". 40.mono still reports `call_sites=0` because a cross-module callee arrives as `NamedVar("lib.pick_second")` with a module-local `SymbolId`. Not a regression: no commit ever had it green. | `doc/08_tracking/bug/stage1_lexer_hir_fatals_eprint_and_generic_len_helper_2026-08-22.md`; hardening plan §27 |

## NOT tagged, and why — the honest residue

### Candidates that turned out GREEN today (3)
The prompt named these as likely in-development. They are not: they pass.

- `generic_class_impl_template_lowering_spec.spl` — **5/5 PASS**. Impl-method
  templates work; nothing to tag.
- `semantics/union_narrowing_spec.spl` — **10/10 PASS**, consistent with
  `union_narrowing_has_no_grammar_or_runtime_2026-08-21.md` being marked
  RESOLVED for grammar, lowering and exhaustiveness. (That record's
  runtime-execution claim is still explicitly not made; that is a coverage gap,
  not a red test, so it is not a tag target.)
- `driver/mono_pipeline_surfaces_unresolved_generic_spec.spl` — **2/2 PASS**.

Tagging any of these would have marked a passing test as expected-to-fail —
exactly the kind of vacuous flag this session has been undoing.

### Candidates with no failing-test surface (2)
These are real unfinished work but have **no red spec to tag**. Tagging
requires a test; a tag cannot be attached to an absence.

- **Generic struct/class instantiation rewriting** (fixture f01: reaches MIR
  step 4/6, then `unresolved method call: to_text`). Tracked as a hardening-plan
  §27 row against `75f554903ff`. This is a *fixture* in the bootstrap A/B lane,
  not a spec file. **Recommendation: file a spec for it, then tag that spec** —
  do not tag the fixture harness, which also covers passing fixtures.
- **The 33 `MirInstKind` variants with no LLVM arm** (30 of them SIMD/GPU), plus
  the 7-backend fail-open class sweep. As of `f17b8afc66a` these now fail the
  BUILD loudly instead of shipping a dead binary; the unimplemented kinds are
  genuine in-development work, but they surface as a compile error on a program
  that uses them, not as a named red spec. Record:
  `llvm_backend_unlowered_mir_kind_fails_open_2026-08-23.md`. Untagged.

### Not surveyed
This lane deliberately did **not** attempt a full-suite sweep: the box is
shared and loaded, the ≤2-job cap makes ~770 spec runs infeasible in one
session, and — decisively — the recorded DB that would have narrowed the set is
incoherent (above). **The failing set outside `compiler/mono` +
`compiler/semantics/union_narrowing` is therefore unknown and unclassified.**
That is the largest gap in this report and is stated rather than papered over.
Next step for whoever continues: fix the test DB first, then re-derive the
failing set from a real run rather than from candidate lists.

## Counts

- Specs executed: **19**
- Tagged in-development: **1**
- Failing but untagged: **0** (the one failure found was tagged)
- Named candidates that were actually green: **3**
- Named candidates with no test surface, left untagged: **2**
- Suite coverage: partial; see "Not surveyed".

## Mechanism status: tagged specs are INERT today

Verified at origin by the docs lane, and this lane concurs from its own runs:

- `--tag <name>` filtering exists **only in the Rust runner**
  (`src/compiler_rust/driver/src/cli/test_runner/args.rs:24`, forwarded
  `execution.rs:923-925`; `--show-tags` at `:911`; `@tag:qemu` scanned at `:95`).
- `in-development` has **zero** hits in `src/` at origin.
- The **pure-Simple** runner parses only `# @di_test`
  (`test_runner_single.spl:193`) and `# @exec_limit` (`:209`) — there is no
  `@tag:` branch. `skip()`/`pending()` live at
  `src/lib/gc_async_mut/spec/__init__.spl:40-43`.

Therefore the tag applied by this lane **changes nothing at runtime**: the spec
still executes and still fails (re-measured after tagging: unchanged, 0/4). It
is a reviewable marker only, until the core lane lands the semantics. This is
deliberate — it means nothing was silenced by this change.

## Bar applied (`.claude/rules/testing.md`)

A correct spec that fails is a legitimate artifact and must stay RED. The tag
was applied on one side of that line only: it records that a **feature is
unfinished**, never that a spec is inconveniently right. Every tagged spec
carries, inline, a site (file:line) and an explicit **unblock condition** naming
what must become true before the tag is removed. Where this lane was unsure, it
left the item RED and put it in the residue above — which is why the tagged
count is 1 and the residue section is the larger part of this report.
