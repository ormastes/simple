# Bug: `TargetArch` enum-vs-enum name collision breaks `Option<TargetArch>.?` under full-tree scan

- **Date:** 2026-07-18
- **Status:** open (documented; NOT fixed — root cause is the seed interpreter's
  flat global type registry, not the two colliding modules)
- **Area:** Rust seed interpreter (`src/compiler_rust`), global
  `enums`/`classes` registry — same mechanism as
  `doc/08_tracking/bug/duplicate_type_name_collision_audit_2026-07-17.md`
- **Related:** `doc/08_tracking/bug/duplicate_type_name_collision_audit_2026-07-17.md`
  (systemic struct-vs-enum collision audit, same day). That audit's own
  scoping note says the mechanism "only bites when a struct/class collides
  with an enum of the same name" — this instance shows the same registry
  collision **also happens enum-vs-enum**, which the audit did not check for.

## Symptom

`test/feature/usage/architecture_spec.spl` (Feature #ARCH-002/#BM-ARCH-001)
was implemented against `src/lib/common/target.spl` (new `pointer_bytes()`,
`stack_align()`, `max_atomic_width()`, `has_fpu()`, `is_harvard()`,
`endianness()`, `pointer_size()`, `triple_str()`, `triple_str_baremetal()`,
`is_8bit/16bit/32bit/64bit()`, plus new `PointerSize`/`TargetConfig` types
and a `parse_target_arch()` free function). 25/27 assertions pass. The 2
that fail are both `parse_target_arch(name).?` checks:

```
✗ AVR parses from string
  expected TargetArch::AVR to equal true
✗ MSP430 parses from string
  expected TargetArch::MSP430 to equal true
```

`parsed.?` (an `Option<TargetArch>` presence check, expected to yield `bool`)
instead evaluates to the *raw unwrapped enum value* `TargetArch::AVR` /
`TargetArch::MSP430`. All 25 other assertions — including direct
`TargetArch.AVR`/`.MSP430` construction and every method call on them
(`bits()`, `pointer_bytes()`, `stack_align()`, `endianness()`, etc.) — pass
correctly, so `TargetArch` itself resolves fine; only the
`Option<TargetArch>` + `.?` path is corrupted.

## Root cause

`src/compiler/70.backend/backend/backend_selector.spl` declares its own,
unrelated, smaller `enum TargetArch` (`X86_64, Aarch64, Riscv64, Host, Avr,
I8086`) used purely for JIT/AOT backend selection. `src/lib/common/target.spl`
declares a much larger `enum TargetArch` (17 variants incl. `AVR`, `MCS51`,
`MSP430`, `Arm`/`ARM`, etc.) for cross-target codegen. Both are top-level,
same-named, in different modules — the exact pattern the sibling audit doc
tracks, except enum-vs-enum instead of struct-vs-enum.

**Mechanism confirmed via a controlled repro** (isolating one variable —
whether a same-named enum is loaded at all — while holding scope, entry
point (`simple run`), and assertion style fixed): a scratch tree with only
`target.spl` runs `parse_target_arch("avr").?` correctly (`true`). Adding a
second scratch module that declares its own `enum TargetArch` (same shape as
`backend_selector.spl`'s) and pulling it in *only via an unrelated function
import* (`use std.decoy.{decoy_marker}` — `TargetArch` itself is never
name-imported from it) is enough to corrupt resolution: `TargetArch.AVR`
then fails outright with `unknown variant or method 'AVR' on enum
TargetArch`, i.e. the second enum's registration wins in the flat global
registry and shadows the real one. This proves the "same top-level name in
two reachable modules collides at runtime" mechanism from the sibling audit
doc applies enum-vs-enum, not just struct-vs-enum.

**What is *not* independently confirmed:** that `backend_selector.spl`
specifically (as opposed to some other same-named declaration, or an
eager-load/ordering effect specific to the real `simple test` path under
full `SIMPLE_LIB=src`) is *the* trigger for the exact failure seen in
`architecture_spec.spl`. Two details differ between the controlled repro and
the real spec run: (1) the repro's corruption broke *direct* enum
construction, while the real spec run left direct construction/method calls
on `TargetArch.AVR` fully working (25/27 assertions pass, including "AVR has
correct properties") and only broke the `Option<TargetArch>`/`.?` path; (2)
the repro used a synthetic decoy enum, not `backend_selector.spl` itself.
Both differences are consistent with the registry being order/scope
sensitive (as the sibling audit describes — "whichever registers last
wins"), but that means the *precise* trigger for the real spec's failure
mode has not been isolated further than "some same-named `TargetArch`
reachable under full `SIMPLE_LIB=src`" — `backend_selector.spl` is the one
concrete same-named candidate found in-repo, not a proven single root cause.

## Why this is documented, not fixed here

Fixing it means either de-duplicating whichever same-named enum(s) turn out
to be involved, or fixing the interpreter to resolve `Option<T>`/enum boxing
through the caller's lexical binding instead of a flat global registry.
Either fix is a cross-cutting change (compiler backend code or interpreter
core) well outside the scope of a small stdlib addition, and doing it
without first fully isolating the trigger risks curing the wrong collision.
Per the sibling audit's own disposition (85 class-A collisions already
tracked, not all fixed), this is filed as one more confirmed instance of the
mechanism rather than patched inline.

## Suggested next step

Fold into the existing systemic collision-audit lane
(`duplicate_type_name_collision_audit_2026-07-17.md`): extend its scan to
also flag enum-vs-enum (not just struct-vs-enum) same-name collisions
(confirmed reproducible above), then isolate which specific reachable
same-named declaration(s) trigger the `architecture_spec.spl` failure mode
before renaming anything — `backend_selector.spl`'s `TargetArch` is the one
known candidate in-repo, but attribution wasn't narrowed past "some
same-named enum reachable under full `SIMPLE_LIB=src`". Longer-term, the
interpreter's `Option<T>`/enum boxing should resolve `T` through the
caller's lexical binding instead of a flat global registry.

## Verification of current state

```
SIMPLE_LIB=src bin/release/x86_64-unknown-linux-gnu/simple test --no-session-daemon test/feature/usage/architecture_spec.spl
=> Passed: 25  Failed: 2  (both: parse_target_arch(...).? on the enum-collision path)
```
