# Non-discriminating (vacuous) spec family — enumerated sweep

**Date:** 2026-08-08
**Status:** Open — detector landed, top findings proven, remediation outstanding
**Pinned base:** `f6397d726afde9f899cbfbc2dc8aa642bf764b21`
**Corpus:** 19,499 `*_spec.spl` files at that sha
**Detector:** `scripts/check/check-vacuous-specs.shs`

## Why

Four non-discriminating specs were found in a single day, each passing
identically on broken and fixed code: `try_operator_error_propagation_spec.spl`
(6/6 green on both, its own NON-VACUITY comment false), the named-ctor
regression spec (all args in field order, so a positional binder passes too),
the chunked-HTTP boundary spec (14 examples, zero hostile inputs, on a parser
that later yielded a request-smuggling overflow), and the LaTeX range spec
(`to_contain("n")` only, `int` half untested).

That is a family, not four coincidences. This document enumerates it and ships a
repeatable detector.

## Headline result

**All 86 examples of `test/01_unit/compiler/hir/hir_types_spec.spl` execute and
pass while asserting only `expect true`, with the module under test never
imported.**

```
SPEC FILE VERDICT: test/01_unit/compiler/hir/hir_types_spec.spl \
  declared>=86 executed=86 passed=86 failed=0 dropped=0
Results: 86 total, 86 passed, 0 failed
```

The file's real assertions are commented out and the import is commented out:

```
# TODO: Enable when hir module is ready for import
# use std.hir.{TypeId, BinOp, UnaryOp, DispatchMode, CaptureMode}

    it "void_ty returns id 0", tag: ["skip"]:
        # expect TypeId.void_ty().id == 0
        expect true
```

Note `executed=86`, not `dropped=86`: the `tag: ["skip"]` is **not** honored —
these examples really run and really report green. 86 green examples certify the
compiler's HIR type system and observe nothing.

## Detector methodology

Two tiers. Only Tier A is mechanized; that split is deliberate.

### Tier A — syntactic, decidable without semantics

| Code | Signal |
|------|--------|
| `V0_NO_ASSERT_FILE` | file contains zero assertion calls |
| `V1_ZERO_ASSERT` | an `it` block whose body asserts nothing |
| `V2_CONST_ASSERT` | straight-line block where every assertion subject is a constant expression |
| `V3_TAUTOLOGY` | `expect(X).to_equal(X)` — same expression both sides |
| `V4_WEAK_CONTAIN` | `to_contain("<=3 chars")` as a block's only assertion |
| `V5_SHAPE_ONLY` | block asserts only `.len()`/`is_empty`/truthiness, never content |
| `V6_STUB_HELPER` | block's only assertion routes to a `fail("TODO")` helper stub |

### Tier B — input-shape claims, MANUAL BY DESIGN

Inputs that never exercise the failure mode the spec claims to gate: all
happy-path inputs on a parser; arguments supplied in declaration order when the
bug is about order; exactly-divisible dimensions when the bug is about
remainders. **Three of the four seed cases were Tier B.** Detecting these
requires knowing what the bug was, so mechanizing them produces noise that must
be hand-triaged anyway. Apply this checklist manually to the high-risk shortlist:

1. Does any input violate the invariant the spec claims to protect?
2. If the bug is about *order*, does any example use non-declaration order?
3. If the bug is about *remainders/boundaries*, is any input non-exact?
4. On a parser over untrusted input, is any input hostile/malformed/truncated?
5. Does the spec's own "non-vacuity" comment, if present, actually hold?

### Two rules that required semantic care

The naive versions of these produced large false-positive classes, both found by
sampling before publishing any count:

- **Helper delegation.** 3,560 corpus files wrap the assertion in a local helper
  (`fn check(c): expect(c).to_equal(true)`). Treating `check(x)` as "no
  assertion" produced ~12 false `V1` hits per file. The detector now resolves
  local helper fns to whether they ultimately assert (2 rounds, so
  helper-calls-helper resolves).
- **Constant assertions are only vacuous in straight-line blocks.** In
  branch-coverage specs, `check(true)` in one arm is paired with `check(false)`
  in the other, so a wrong branch genuinely fails. `V2` therefore fires only when
  the block has **no control flow** and **every** assertion subject is a constant
  expression (`1 == 1`, `"a" == "a"`, `true`). Fixture F7 guards this exemption.

### Empirically-corrected assertion vocabulary

`expect` also has a **paren-less statement form** — `expect diagram_args.len() ==
3`, and after a match arm `case nil: expect false`. It is a registered builtin of
arity 1 (`src/compiler/30.types/type_system/builtin_registry.spl:155`).

**This form does assert** — probe result: a spec containing only `expect false`
reports `executed=2 passed=0 failed=2`, exit 1. Missing it made `V1_ZERO_ASSERT`
fire falsely on real assertions across 1,322 files (33,564 uses). Correcting it
dropped `V1` from 1,300 files to 251 and `V0` from 1,181 to 232.

### Fail-closed design and injection-test proof

This repo has a documented history of sweep oracles failing open. The detector
runs `--selftest` **before every scan, fatally**, over 8 fixtures:

| Fixture | Shape | Must |
|---------|-------|------|
| F1 | `expect(true).to_be_true()` | FLAG |
| F2 | exact `to_equal` on a computed value | not flag |
| F3 | vacuous assertion **not on line 1**, valid content above | FLAG — catches an anchored regex without a multiline flag matching only line 1 |
| F4 | spec at a **deep nested path** | FLAG — catches a path filter missing the tree prefix reporting "0 candidates" as a clean sweep |
| F5 | helper-delegated **real** assertion | not flag |
| F6 | straight-line block, all assertions constant expressions | FLAG |
| F7 | branch-coverage `check(true)`/`check(false)` | not flag |
| F8 | paren-less `expect <expr>` on a computed value | not flag |

Negative controls verified (the selftest can actually fail):

- Sabotaging `has_assert` to always return 0 → `SELFTEST FAILED … refusing to
  scan`, exit 2.
- Empty root → `ERROR — nothing was checked`, exit 2. A zero-candidate sweep is
  never a pass.
- Nonexistent root → exit 2.
- `scanned` is summed across **all** `xargs`-split awk invocations and reconciled
  against the listed file count; a mismatch is `ERROR`, not a partial pass.

Verdict is always the last line: `PASS — <n> files scanned, <m> flagged`.

## Results at the pinned sha

`PASS — 19499 files scanned, 33568 flagged`

| Code | Rows | Files |
|------|------|-------|
| `V2_CONST_ASSERT` | 25,406 | 3,427 |
| `V5_SHAPE_ONLY` | 2,276 | 1,023 |
| `V4_WEAK_CONTAIN` | 2,180 | 547 |
| `V1_ZERO_ASSERT` | 1,995 | 251 |
| `V3_TAUTOLOGY` | 1,449 | 343 |
| `V0_NO_ASSERT_FILE` | 232 | 232 |
| `V6_STUB_HELPER` | 30 | 6 |
| **distinct files** | | **5,428** (27.8% of corpus) |

`test/unit/` and `test/01_unit/` (likewise `system`/`03_system`,
`integration`/`02_integration`, `perf`/`05_perf`) are **byte-identical mirror
trees**, so every finding is counted twice. **Collapsing mirrors: 3,150 distinct
specs.**

### On the prior 22,039/15% vs 513-examples/45-files contradiction

**Neither figure is reproducible, because neither names a base commit**, and the
task was right not to treat either as settled. This sweep supports *neither*
directly. What this sweep states, with the base pinned:

- **3,150 distinct specs (5,428 counting mirrors) carry at least one Tier-A
  syntactic vacuity candidate** at `f6397d72`.
- That is **candidates**, not proven-vacuous specs. Only the subset below is
  empirically proven. Conflating those two claims is how the earlier numbers
  became unusable, so they are reported separately here.

`origin/main` moved **three times during this session** (`1c04408` → `0c4d480` →
`f6397d7`), which is why an immutable sha, not a moving ref, is the base.

## Risk-ranked findings

Ranked by what a green verdict falsely certifies, not by how vacuous it looks.
Mirror duplicates collapsed.

| # | Spec | Vacuous blocks | Gates | Risk | Proof |
|---|------|---------------:|-------|------|-------|
| 1 | `test/{01_,}unit/compiler/hir/hir_types_spec.spl` | 86 | compiler HIR type system | **critical** | PROVEN: 86/86 green, import commented out |
| 2 | `test/{01_,}unit/compiler/hir/hir_eval_spec.spl` | 82 | compiler HIR evaluation | **critical** | PROVEN: 82/82 green |
| 3 | `test/{01_,}unit/compiler/hir/hir_module_spec.spl` | 59 | compiler HIR module | **critical** | candidate, same shape |
| 4 | `test/{01_,}unit/compiler/hir/hir_lower_spec.spl` | 56 | HIR→MIR lowering | **critical** | candidate, same shape |
| 5 | `test/{01_,}unit/compiler/parser/treesitter_parser_real_spec.spl` | 41 | parser core ("Real Implementation Tests") | **critical** | candidate; assertions commented out, Status: Planned |
| 6 | `test/{01_,}unit/compiler/parser/treesitter_lexer_real_spec.spl` | 38 | lexer core | **critical** | candidate, same shape |
| 7 | `test/{feature,03_system/feature}/usage/parser_declarations_spec.spl` | 19 | parser declarations | high | candidate |
| 8 | `test/03_system/feature/compiler/bootstrap_system_spec.spl` | 14 | bootstrap/self-host | high | candidate |
| 9 | `test/{feature,03_system/feature}/usage/parser_skip_keyword_spec.spl` | 11 | parser keyword handling | high | candidate |
| 10 | `test/01_unit/os/compositor/compositor_occlusion_spec.spl` | 10 | OS compositor occlusion | high | candidate |
| 11 | `test/01_unit/compiler/frontend/parser_spec.spl` | 10 | frontend parser | high | candidate |
| 12 | `test/{01_,}unit/std/deep/dict_deep_4_spec.spl` | many | claims "STDLIB Deep-Dive / dict"; asserts `check(1 == 1)`, `check("a" == "a")` | med-high | candidate; body contains no dict symbol |

**900 `V2` files sit in high-risk domains** (compiler / parser / os / codegen /
crypto / net / memory) after excluding other lanes' paths.

### The dominant sub-family: commented-out assertion + live `expect true`

**51 files** have both a commented-out assertion and a live constant-assert
block; **25 of them are in high-risk domains**. This is the single most
productive pattern: an assertion was disabled pending a module, replaced with
`expect true`, and the spec kept reporting green ever since. Findings #1–#9 are
all this shape.

The `hir_*` family alone is **283 green examples per mirror tree (566 total)**
certifying the compiler's own HIR while importing nothing.

## Off-limits (other lanes own these)

Excluded from ranking and remediation, listed so the enumeration stays complete:
`try_operator_error_propagation_spec.spl`; the named-ctor regression spec; the
chunked-HTTP specs; the LaTeX range spec; AES/crypto specs; `struct_field_order`;
the shape-(d) refactor family.

## Reproducing

```sh
sh scripts/check/check-vacuous-specs.shs --selftest          # 8 fixtures, fatal
sh scripts/check/check-vacuous-specs.shs --root . --tsv      # full sweep
```

Pin the corpus first for a stable count:

```sh
git archive <sha> $(git ls-tree -r --name-only <sha> | grep '_spec\.spl$') | tar -x -C /tmp/pin
sh scripts/check/check-vacuous-specs.shs --root /tmp/pin --expect-files 19499 --tsv
```

## Harness caveat observed

A one-line trivially-passing spec under `src/lib/**/test/` reports `SPEC FILE
VERDICT … passed=1 failed=0` while also printing `Results: 0 passed, 1 failed`
and exiting 1. Another lane is root-causing this; findings here avoid that path.
Not attributable to this sweep.

## Remediation

1. The `hir_*` family (#1–#4) and `treesitter_*_real` (#5–#6) must either import
   and assert against the real module, or be marked failing per
   `.claude/rules/testing.md` ("a correct spec that fails is a legitimate
   artifact"). They must not keep reporting green.
2. Wire `check-vacuous-specs.shs` into the pre-commit/CI check set so new
   `expect true` placeholders cannot land silently.
3. Work the remaining 900 high-risk `V2` files by descending block count.
4. Apply the Tier-B manual checklist to the high-risk shortlist.
