# DO-330 Tool-Qualification Validation Corpus

Independent-oracle evidence for the pure-Simple self-hosted compiler
(`bin/release/<triple>/simple`), per
`doc/03_plan/cert/tool_qualification_plan.md` (cert Phase-7 / deferred task C7).

Runner: `scripts/check/cert/run-tool-qual-corpus.shs`
(`--self-test`, `--help`, exits non-zero on any defect).

Freeze tool: `scripts/check/cert/freeze-tool-qual-golden.shs` — writes a NEW
`.expected` golden for a `positive/` case from a caller-supplied value; refuses
to overwrite an existing golden unless `--force` (`--help` for usage).

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
positive/   17 cases, one per language-construct family, each with a .expected golden
              arithmetic/precedence, structs+fields, custom enum+match+payload,
              closures, generics, recursion, integer/bitwise ops, text ops,
              booleans/short-circuit, trait+default-method (override path),
              struct-field composition, type-qualified static calls,
              closure composition (sibling closures), bounded generics,
              tuples/multi-return, string interpolation, array/list ops
negative/   8 cases that MUST be rejected
              undefined symbol, unknown struct field, parse error (unclosed
              paren), undefined function, undefined struct type, undefined
              module import, reserved keyword as identifier, parse error
              (missing colon)
known_defects/  OPEN tool defects (silent-accepts / crashes the deployed binary
              currently exhibits). NOT walked by the runner's gate — see its
              README. These are documented, reproducible findings, seeding the
              plan's `known_problem/` category, not a pass/fail gate.
```

Custom enums are used (not built-in `Result`/`Ok`/`Err`/`?`, which are
frozen-buggy on the deployed binary) so `enum + match + payload` codegen is
exercised without masking by that known frozen path.

## Scope (honest)

This corpus (plan §5 step 1–4, expanded) covers the core value-computing
construct families, a first pass at traits/composition/module-qualified-calls/
generics-with-bounds/tuples/string-interpolation/array-ops, and eight reject
classes. It does **not** cover actors/async/ffi/memory-tiers positives, the
full diagnostic-code matrix, or the `meta/` tool-property tests (determinism /
opt-invariance). Those remain future work. The corpus is runnable **now** on
the clean deployed binary and is GREEN; the discovered silent-accept/crash
defects are recorded under `known_defects/` rather than hidden.

Several constructs in the requested breadth were **skipped from `positive/`**
because they misbehave on the deployed binary (an unsound "positive" case
would defeat the point of an independent oracle); each is instead a
reproducible `known_defects/` entry:
- Calling a trait **default** method that is inherited (NOT overridden in the
  `impl`) segfaults — `known_defects/trait_default_method_inherited_segfault.spl`.
  `positive/10_traits_default_methods.spl` covers only the explicit-override
  path, which is sound.
- `mixin`-based composition (`use SomeMixin` inside `class` or `struct`) is
  broken both ways: on `class` it silently runs (exit 0) and prints garbage
  values (`known_defects/mixin_class_use_garbage_value.spl`); on `struct` it
  silently runs (exit 0) and leaks a fabricated error string to stdout
  (`known_defects/mixin_struct_use_runtime_error.spl`).
  `positive/11_composition.spl` uses plain struct-field composition +
  explicit delegation instead, which is sound and is the documented
  no-inheritance idiom.
- A closure **lexically nested** inside another closure's body, reading a
  variable captured by the *enclosing* closure, silently computes the wrong
  value (`known_defects/nested_closure_capture_wrong_value.spl`) — matches the
  known "nested closure capture" runtime limitation, but even the *read-only*
  path is unsound, not just the write path.
- A closure that captures a function parameter and is **returned across the
  function boundary** prints an invalid-heap-pointer tag when later called
  (`known_defects/closure_return_across_function_boundary_invalid_heap.spl`).
  `positive/13_closures_compose.spl` uses two sibling closures at the same
  scope instead, which is sound.
