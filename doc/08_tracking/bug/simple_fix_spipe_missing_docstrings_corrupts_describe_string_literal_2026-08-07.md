# `bin/simple fix` on `spipe_missing_docstrings` corrupts `describe "..."` string literals

**Found:** 2026-08-07, during notebook-lanes K1 implementation
(`test/01_unit/lib/notebook/kernel_session_manager_spec.spl`).

## Symptom

Running `bin/simple fix <spec file>` with the `spipe_missing_docstrings` lint rule
active, against a spec containing a bare `describe "..."` block with no docstring,
injects the generated docstring text into the middle of the `describe` string literal
instead of inserting a new docstring line after the block header. This corrupts the
string literal and breaks parsing of the file.

## Repro

```bash
bin/simple fix test/01_unit/lib/notebook/kernel_session_manager_spec.spl
```

against a spec with:

```simple
describe "KernelSessionManager":
    it "creates a session with a default mode":
        ...
```

and no `"""..."""` docstring under the `describe` header.

## Impact

Any spec file with a bare `describe` (no docstring) that runs `bin/simple fix` with
this rule enabled gets its `describe` line corrupted and fails to parse afterward. The
fix was caught and manually reverted before landing; not yet root-caused in the fixer's
implementation.

## Status

Open — not yet investigated further. Recommend avoiding `bin/simple fix` on spec files
with `spipe_missing_docstrings` active until fixed, and adding a spec such as this one
as a regression case once the fixer's insertion-point logic is corrected.
