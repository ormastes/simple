# ADR — Negative slice step is not part of the language

- **Status:** Accepted
- **Date:** 2026-07-30
- **Owners:** Language / slicing semantics
- **Context doc:** `test/03_system/feature/usage/negative_step_slice_spec.spl`,
  `test/03_system/feature/usage/advanced_indexing_spec.spl`

## Context

Simple's slice expression `s[start:end:step]` allows all three parts to be
omitted independently. Two distinct features were both reachable through this
one syntax and were being conflated:

1. **Negative indices** (Ruby-style, count from the end): `s[-3:]`,
   `s[0:-1]`, `arr[-4:-1]`. These are a normal, supported part of indexing —
   fully independent of step and already correct in both execution engines.
2. **Negative step** (Python-style): `s[::-1]`, `s[9:0:-1]`. This reverses
   the sliced range by walking it backwards.

Probing both engines against `s[9:0:-1]` and a battery of related forms
(before any code change) showed neither engine treated negative step as
intentional, supported behavior, and the two engines disagreed with each
other:

- **Default/native (JIT) engine:** `rt_slice` (native runtime,
  `src/compiler_rust/runtime/src/value/collections.rs`) — the string branch
  treated *any* `step != 1` as "return an empty string"; negative step
  silently produced `""` with no error and exit code 0. (The array branch
  happened to already implement full Python-style reversal — an
  undocumented, untested divergence from the string branch in the same
  function.)
- **Interpreter engine** (`SIMPLE_EXECUTION_MODE=interpret`,
  `src/compiler_rust/compiler/src/interpreter/expr/collections.rs`):
  silently implemented full Python-style negative-step reversal, correctly,
  for strings and arrays alike.

So the same source line `s[9:0:-1]` returned `""` under the default engine
and a correctly-reversed string under the interpreter, with no diagnostic
either way.

A third, independent implementation was found in the pure-Simple SimpleOS /
baremetal runtime tier, `src/runtime/simple_core/core_string.spl`'s own
`rt_slice` (used by binaries built for the `nogc_async_mut_noalloc` tier,
which cannot link the hosted Rust `runtime` crate). It diverged a third way:
its array branch silently implemented full Python-style reversal (matching
the interpreter), while its string branch silently clamped any `step < 1` to
`1` — a forward slice that ignores the sign entirely, not empty and not
reversed. No `src/` call site constructs a negative step deliberately, but
this function itself is production code, and it is now fixed the same way
(guarded, matching this file's own pre-existing convention of returning the
nil sentinel `3` for `step == 0`, since this baremetal tier has no
stderr/abort story of its own). Outside of that, the only place negative
step was exercised was the test suite (4 spec files under `test/`), where it
"worked" only because `bin/simple test` runs under the interpreter.

## Decision

**Negative slice *step* is not part of the language and is a hard error in
both engines.** Negative *indices* remain fully supported and are unaffected
by this decision — reversal is always an explicit method call:

```
arr.reversed()      # not arr[::-1]
s.reversed()         # not s[::-1]
```

`s[9:0:-1]`, `s[::-1]`, `s[::-2]`, and any other slice with `step < 0` now
raise a diagnosable error naming `.reversed()` as the correct idiom, in both
the interpreter and the default/native engine.

## Language survey

Surveyed languages with slicing or range-based substring/subarray syntax:

| Language | Negative-step slice syntax | Reversal idiom |
|---|---|---|
| Python | `s[::-1]` (yes — the outlier) | also has `reversed(s)` |
| Ruby | not supported | `s.reverse` |
| Rust | not supported | `s.iter().rev()`, `s.chars().rev()` |
| Go | not supported | explicit loop / `slices.Reverse` |
| JavaScript | not supported | `arr.reverse()`, `[...s].reverse()` |
| Java | not supported | `Collections.reverse(list)` |
| C# | not supported | `Enumerable.Reverse()` |
| Kotlin | not supported | `list.reversed()` |
| Swift | not supported | `s.reversed()` |
| C++ | not supported | `std::reverse(begin, end)` |
| Simple (this decision) | not supported | `.reversed()` |

Python is the lone outlier that overloads slice syntax with a step to mean
"walk backwards." Every other surveyed language keeps subrange selection
(possibly with negative, from-the-end indices) and reversal as two separate
operations. Simple's negative-index support already matches the from-the-end
half of Ruby's model; this decision aligns the reversal half with the same
majority (and with Ruby specifically, since Simple already follows Ruby for
indices).

## Rationale

1. **Byte-based reversed slicing shreds UTF-8, and collides with the
   character-alignment migration.** A byte-indexed negative-step slice over
   a UTF-8 string walks backwards one byte at a time, which is not a valid
   operation on multi-byte codepoints — it produces corrupt output or a
   panic depending on where the walk lands mid-codepoint. A sibling lane is
   independently migrating Simple's string indexing/slicing primitives from
   byte-aligned to character-aligned semantics; adding negative-step
   semantics on top of that primitive at the same time is exactly the kind
   of two-axis change this repo's process avoids. Removing negative step
   entirely sidesteps the interaction rather than requiring the
   character-alignment lane to also define reversed-walk semantics. (Unit
   alignment — byte vs. character indexing — is the sibling lane's decision;
   this ADR does not take a position on it and cross-references rather than
   contradicts it.)
2. **Even correct codepoint-reversal breaks combining marks and emoji ZWJ
   sequences.** This is not a Simple implementation gap — it is Python's own
   documented wart. `"noél"[::-1]` in Python does not produce `"lén"` — it
   detaches the accent from the vowel it combines with, because codepoint
   reversal treats a base character and its combining mark as two
   independent, swappable units. The same failure applies to any
   grapheme-cluster sequence: regional-indicator flag pairs and ZWJ emoji
   sequences (`"👨‍👩‍👧"`) both corrupt under naive reversal. A method-based
   `.reversed()` is free to define (now or later) grapheme-cluster-aware
   reversal; an index-trick can never be given that opportunity because it
   has no privileged position for special-casing composed sequences.

## Consequences

### Positive

- One reversal idiom (`.reversed()`), consistent across arrays, strings, and
  tuples, with a single place to fix or extend semantics (e.g. grapheme-aware
  reversal) later.
- Removes the two-engine divergence found during probing (empty-string vs.
  full-Python-reversal for the same source line) — an error in both engines
  is safer than either silent behavior.
- No longer forces the character-alignment migration to also define
  negative-step walk semantics.

### Negative / follow-ups

- Four pre-existing spec files (`collections_spec.spl`,
  `advanced_indexing_spec.spl`, `range_step_by_spec.spl`, `tensor_spec.spl`,
  plus their `test/feature/...` duplicates) asserted negative-step slicing
  as working, Python-style behavior. These were rewritten to use
  `.reversed()` in the same change as this decision.
- The default/native engine reports the error via `eprintln!` +
  `std::process::abort()` (exit code 134 / SIGABRT on Linux), matching the
  existing `rt_panic` fatal-error idiom for that lane, since there is no
  `Result`-returning path back through JIT/native-compiled code to a
  catchable Simple-level error for a slice **expression**. The interpreter
  reports it as a normal `CompileError` (exit code 1). Both name
  `.reversed()` in the message; the differing exit codes are an accepted,
  pre-existing asymmetry between the two engines' fatal-error mechanisms,
  not something this change introduces.
- The SimpleOS/baremetal runtime tier's `rt_slice`
  (`src/runtime/simple_core/core_string.spl`) returns the same nil sentinel
  (`3`) it already uses for `step == 0`, rather than aborting or raising —
  that tier has no stderr/abort convention of its own, and this matches its
  existing local error idiom rather than importing a hosted-process
  mechanism that doesn't apply there. Board-runnable verification of this
  path is unclaimed by this change; it is a pure-Simple source fix following
  the same pattern as the two hosted engines, not independently verified on
  QEMU or hardware as part of this ADR.

## Acceptance check

- [x] ADR filed at
      `doc/04_architecture/language/slicing/+adr/negative_step_not_supported_2026-07-30.md`.
- [x] Both engines raise a diagnosable error for `step < 0`, naming
      `.reversed()`.
- [x] Error-asserting spec at
      `test/03_system/feature/usage/negative_step_slice_spec.spl` covers bare
      reverse, bounded reverse, step -2, and negative-index + negative-step
      combined, plus a negative-index-only regression guard.
- [x] Negative-index-only behavior (`s[-3:]`, `arr[-4:-1]`, etc.) verified
      unaffected in both engines.
- [ ] `doc/07_guide/quick_reference/syntax_quick_reference.md` and other
      slicing guide docs updated to describe the bracket form without a
      negative-step example (tracked in the same change).
