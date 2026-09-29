# DO-330 Tool-Qualification Validation Corpus

Independent-oracle evidence for the pure-Simple self-hosted compiler
(`bin/release/<triple>/simple`), per
`doc/03_plan/cert/tool_qualification_plan.md` (cert Phase-7 / deferred task C7).

Runner: `scripts/check/cert/run-tool-qual-corpus.shs`
(`--self-test`, `--help`, exits non-zero on any defect).

## Why this corpus exists

The 3-stage bootstrap proves `stage2 == stage3` (byte-identical): the compiler
compiles itself to a fixed point. That is **self-consistency, not correctness** —
a systematic miscompile present in stage2 is reproduced identically into stage3
and survives the fixpoint invisibly. DO-330 requires an **independent oracle**:
an expected result derived *outside* the tool under test. This corpus is that
oracle.

## Oracle-independence policy

- **positive/** — each `<case>.spl` has a sibling `<case>.expected` golden whose
  content is the **spec / hand-computed** result of the program (the value is
  written in a comment at the top of each `.spl` and cross-checked by hand:
  e.g. `5 + 6*7 = 47`, `fib(10) = 55`, `3*5 = 15`). The golden is the authority;
  the compiler is **never** allowed to define its own pass criterion. Each golden
  in this initial drop was cross-checked: the value hand-derived from the
  language spec **equals** the value observed from the tool. Where those two
  disagree, the golden must hold the spec value and the divergence is a finding —
  none diverged in this drop.
- **negative/** — each `<case>.spl` is an invalid program that MUST be rejected:
  non-zero exit **and** empty stdout (a truthful diagnostic on stderr). A
  negative case that compiles+runs clean is a silent-accept defect (TOR-FM-02).
- Only **stdout + exit status** are evidence. stderr carries the `[INFO]` JIT
  fallback line and diagnostics and is not pinned.

## Golden immutability

`.expected` files are pinned certification evidence. They are produced **once**,
by observing the tool **and** cross-checking against the independently-derived
spec value, and must not be regenerated to match a regressed compiler. A golden
change is a deliberate, reviewed re-baseline — per the plan, gated by a
`TOOLQUAL-REBASELINE: <reason>` commit token (pre-commit hook, plan §2.3). The
runner never writes goldens.

## Layout

```
positive/   9 cases, one per language-construct family, each with a .expected golden
              arithmetic/precedence, structs+fields, custom enum+match+payload,
              closures, generics, recursion, integer/bitwise ops, text ops,
              booleans/short-circuit
negative/   4 cases that MUST be rejected
              undefined symbol, unknown struct field, parse error, undefined function
known_defects/  OPEN tool defects (silent-accepts the deployed binary currently
              exhibits). NOT walked by the runner's gate — see its README. These
              are documented, reproducible findings, seeding the plan's
              `known_problem/` category, not a pass/fail gate.
```

Custom enums are used (not built-in `Result`/`Ok`/`Err`/`?`, which are
frozen-buggy on the deployed binary) so `enum + match + payload` codegen is
exercised without masking by that known frozen path.

## Scope (honest)

This is the **initial** corpus (plan §5 step 1–4 partial): it covers the core
value-computing construct families and the three reject classes named in the
plan. It does **not** yet cover traits/mixins/modules/actors/async/ffi/memory-
tiers positives, the full diagnostic-code matrix, or the `meta/` tool-property
tests (determinism / opt-invariance). Those remain future work. The corpus is
runnable **now** on the clean deployed binary and is GREEN; the discovered
silent-accept defects are recorded under `known_defects/` rather than hidden.
