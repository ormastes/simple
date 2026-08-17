# `regeneration_spec` asserts a `conversion_is_safe` theorem that exists nowhere

- **Filed:** 2026-08-17
- **Status:** OPEN — needs a formal-model decision, not a test edit
- **Severity:** medium (1 RED example in the formal-verification suite)
- **Spec:** `test/00_formal_verification/compiler/regeneration_spec.spl:22-26`
- **Generator:** `src/compiler_rust/lib/std/src/verification/regenerate/memory_capabilities.spl`

## Symptom

`Results: 4 total, 3 passed, 1 failed`

```
✗ regenerates memory capability output
```

Reproduced independently twice (the pass-2 runner and a direct
`--timeout 800` run), so it is not a timeout artifact.

The example asserts three things about the generated Lean:

```
val lean_code = regen_mem_cap.regenerate_memory_capabilities()
expect(lean_code).to_contain("inductive RefCapability")   # present
expect(lean_code).to_contain("def canConvert")            # present
expect(lean_code).to_contain("theorem conversion_is_safe") # NOT present
```

The harness prints the whole generated document as the failure subject, which
truncates in the log and makes it look as though generation stopped early. It
does not — `memory_capabilities.spl` is straight-line `add_raw_line` calls with
no early return between `getActiveRefs` (line 45) and `def canConvert`
(line 67). The generated text is complete; the third `to_contain` is what fails.

## Measured

`conversion_is_safe` does not exist anywhere in the tree:

```
$ grep -rn 'conversion_is_safe' src/ --include=*.spl
(no output)
```

The generator emits **four narrower** conversion theorems instead
(`memory_capabilities.spl:105-131`):

- `can_convert_refl` — `canConvert cap cap = true`
- `exclusive_to_shared` — `canConvert RefCapability.Exclusive RefCapability.Shared = true`
- `isolated_to_exclusive`
- `isolated_to_shared`

The committed golden Lean file carries exactly those four names and no
aggregate. So **generator and golden output agree with each other**; only the
spec disagrees with both.

## Why this was NOT fixed by editing the assertion

Two readings, and they call for opposite changes:

1. **Stale name.** The assertion is a rename/typo artifact and should point at
   `can_convert_refl` (or assert all four). Cheap, and makes the suite green.
2. **Genuinely missing theorem.** This is a *formal-verification* suite, where
   the spec plausibly IS the specification: it may be asserting that the model
   ought to prove an aggregate conversion-safety property, and the generator
   never implementing one is the actual gap. The four theorems are instances,
   not a general safety statement — notably there is no theorem saying the
   *disallowed* conversions are rejected, which is the half an aggregate
   `conversion_is_safe` would most likely cover.

Editing the assertion under reading (1) would erase the evidence for reading
(2). Needs the owner of the memory-capabilities formal model to choose.

## Repro

```
bin/simple test test/00_formal_verification/compiler/regeneration_spec.spl --timeout 800
```

Note: `SIMPLE_TIMEOUT_SECONDS` does **not** work here — see
`doc/08_tracking/bug/simple_timeout_seconds_ignored_by_light_daemon_budget_2026-08-17.md`.
