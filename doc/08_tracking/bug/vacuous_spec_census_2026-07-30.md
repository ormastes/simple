# Vacuous-spec census: 905 specs and ~14,500 test cases are disabled behind fake-green placeholders

**Lane PLACEHOLDER1**, run inline by the orchestrator after the subagent was
halted on an API quota. Method is shell counting over `test/01_unit/**` and
`test/unit/**`; every number below is reproducible with the commands recorded
here.

## The pattern

Lane QSK1 needed specs to validate a 31-file rename and found all five of its
"relevant" specs looked like this:

```
describe "Builder Api":
    it "skipped":
        val pending_reason = "pre-existing test failures - functions/imports not available"
        expect(pending_reason.len()).to_be_greater_than(0)

# # Builder API Tests - Fluent Block Building
# use compiler.blocks.builder.{BlockBuilder}
# describe "BlockBuilder - Construction":
#     it "builds an empty block":
# ...470 more commented-out lines
```

The real test file is **commented out wholesale** and replaced by one assertion
that cannot fail — `expect(pending_reason.len()).to_be_greater_than(0)` is true
by construction. The suite reports `1 total, 1 passed, 0 failed` and goes green.

## Counts

| Shape | Count |
|---|---|
| Spec files scanned (`test/01_unit` + `test/unit`) | 16,253 |
| Files containing `pending_reason` | 1,154 (**7.1%**) |
| Files containing `it "skipped"` | 1,141 |
| **Unique specs after mirror-dedup** | **905** |
| Files with commented-out `describe` blocks | 699 |
| **Commented-out `it "..."` test cases** | **14,535** |
| Files with zero `expect` anywhere | 238 |

`test/unit/` is a known 884-file-diverged mirror of `test/01_unit/`, so the
deduped **905 specs / ~14,500 cases** is the honest figure.

By area (deduped): lib 317, compiler 240, app 225, compiler_core 91, std 18,
compiler_shared 8, os/memleak/bugs 6.  **331 of the 905 guard compiler internals.**

## The reasons are hidden failures, not pending features

This is the finding. Distribution of `pending_reason` strings:

| n | reason |
|---|---|
| 459 | `pre-existing test failures - functions/imports not available` |
| 103 | `imports compiler modules - causes OOM via numbered directory resolution` |
| 98 | `assertion failures - runtime behavior differs in interpreter mode` |
| 31 | `function 'tensor_from_data' not found in interpreter runtime` |
| 24 | `method 'randn_1d' not found on 'dict'` |
| 16 | `module 'compiler_shared.diagnostics' not resolvable` |
| 12 | `variable 'indent_level' not found - struct field access or scope issue` |
| 12 | `std.exp.* path unresolvable from nogc_sync_mut/src/` |
| 12 | `function 'tensor_randn' not found in interpreter runtime` |
| 11 each | `Conv2d__create` / `MaxPool2d__create` not found in interpreter runtime |
| 10 | `timeout - module loading exceeds 60s` |

Not one of the top reasons is "this feature isn't built yet." Every one is a
**symptom of a real defect** — and several name defects this repo has already
documented separately: interpreter-vs-native divergence, dict method dispatch,
module-resolution OOM, the 60s timeout.

The repo rule is *"NEVER skip failing tests without approval."* 905 specs were
skipped, and the failure reason was preserved in a string as the only trace.

## Verification attempted

Re-enabled `builder_api_spec.spl` by uncommenting its body into a scratch spec
and running it: `Results: 1 total, 0 passed, 1 failed`. The underlying breakage
is still present, so these are not stale placeholders guarding already-fixed
code. **Caveat, stated because it matters:** the uncomment was a crude `sed`, and
only 1 of the file's many `describe` blocks registered — so this shows the spec
does not trivially pass, not that all 14,535 cases still fail. A rigorous
re-enable pass is a separate lane.

## Why no bulk repair was done

Re-enabling 905 specs would surface an unknown but large number of real failures
at once. That is the honest state of the tree, but flipping it in one change is a
call for the repo owner, not a lane — and this repo explicitly forbids both
skipping failing tests *and* mass-changing test state without approval.

## Recommendation

1. **Stop the bleeding:** treat `pending_reason` as a lint-detectable anti-pattern
   so no new ones land silently.
2. **Re-enable by cluster, not by file.** The 459 + 98 + 103 groups share root
   causes; fixing one defect likely revives dozens of specs at once. Start with
   the 103 OOM-on-numbered-directory-resolution group, which is one bug.
3. **Report the real number.** Any statement of suite health that counts these
   905 as passing is overstated by ~14,500 cases.

---

# Addendum 2026-08-01 — a third vacuity shape: the spec ships a copy of its subject

The census above covers **file-level** vacuity (body commented out behind a
`pending_reason` / `it "skipped"`). A separate lane covers **assertion-level**
vacuity (SPIPE005: bodies that run but assert nothing). Neither detector sees a
third shape, which is the most misleading of the three because the file looks
like a complete, well-organised, fully-green spec:

**Shim vacuity** — the spec contains a *local reimplementation* of the module it
names, and asserts against the copy. Every example runs, every assertion is a
real assertion, the summary is green, and nothing the shipped code does can ever
change the result.

## Worked case (PROVED)

`test/{01_unit,unit}/app/test_runner/args_spec.spl` opened with

    # Tests for test_runner_args.spl:
    #  - parse_mode_str, parse_test_args

and then defined its own 190-line `parse_test_args` plus its own
`TestExecutionMode`/`TestLevel` enums. It imported nothing. Baseline:
`71 total, 71 passed, 0 failed`.

Because the copy was never reconciled with the shipped parser, it had drifted in
six ways — all of which the spec asserted *as correct*:

| assertion in the copy | shipped `test_runner_args.spl` |
|---|---|
| default `format == "default"` | `"text"` |
| field `has_seed` | field is `seed_set` |
| `mode` is `text` | `mode` is `TestExecutionMode` |
| "ignores second positional argument" | both positionals retained in `paths` |
| `--capture-screenshots` / `--screenshots` / `--refresh-screenshots` / `--refresh-gui-image` / `--screenshot-output` set `capture_screenshots`, `refresh_gui_images`, `screenshot_output` | **none of these flags or fields exist**; the validator answers `unknown option: --screenshots` |
| `parse_mode_str` has 3 outcomes | also `Compile` and `Composite(...)`, incl. `interpreter(...)` normalisation |

The multi-path row is the sharpest: this spec pinned, as expected behaviour, the
exact defect that `1cfed202c53` had to fix (`simple test a.spl b.spl` running
only the first path). It stayed green through both the bug and the fix.

## Non-vacuity proof (PROVED)

Three one-line sabotages to the **shipped implementation**
`src/lib/nogc_sync_mut/test_runner/test_runner_args.spl` — default `timeout`
120→999, `parse_mode_str` losing the `smf`/`loader` arm, and `--tag` discarding
its value — run against four specs in the same tree, same binary, same command:

| spec | under sabotage |
|---|---|
| `args_spec.spl` (rewritten) | 92 total, **5 failed** |
| `config_parser_spec.spl` (rewritten) | 16 total, **3 failed** |
| `args_spec.spl` **as it was at base** | 71 total, 71 passed, **0 failed** |
| `config_parser_spec.spl` **as it was at base** | 9 total, 9 passed, **0 failed** |

An earlier sabotage set (timeout 120→999, `binary` dropped from `parse_mode_str`,
`--fail-fast` neutered) put the rewritten `args_spec` at **6 failures** with the
original still at 71/71. The originals cannot go red because they never load the
file being sabotaged.

Both rewritten specs are green against unmodified source: 92/92 and 16/16.

## Scale of the shape (INFERRED — static, and an upper bound)

Static scan of 18,862 `*_spec.spl` files: **736 files** (376 unique after the
`test/01_unit` ≡ `test/unit` mirror dedup) have **no implementation import** and
define a function whose distinctive name is also defined under `src/`,
totalling **15,366 live examples**. This is an upper bound: some of those local
functions are genuine test helpers that merely share a name (`float_eq`,
`side_effect`). It is not a verdict on any individual file, only a work queue.

Report the three shapes separately — the repairs are unrelated. File-level
vacuity needs its body restored or the file deleted; assertion-level vacuity
needs assertions added; shim vacuity needs the local copy **deleted** and the
subject imported, and it is the only one of the three that will surface real
API drift the moment it is fixed.

## Detector warning

A first pass at the shim-vacuity count returned **3,118** files. The inflation
was a single generic helper name, `check`, which exists both in `std.spec` and
in hundreds of specs. Filtering generic names cut it to 736 — a **4.2×**
correction, the same failure mode that inflated the earlier `expect(`-only
census 4.7×. Any count of this shape must exclude generic helper names and be
reported as an upper bound.

## Engine reach

All results above come from `bin/simple test` on the 154,185,152-byte Rust
bootstrap seed, which runs the tree-walking interpreter. `parse_test_args` is
pure argument handling with no engine-specific behaviour, so the evidence
transfers; but no spec in this batch reaches the JIT or native lanes, and no
claim here should be read as covering them.
