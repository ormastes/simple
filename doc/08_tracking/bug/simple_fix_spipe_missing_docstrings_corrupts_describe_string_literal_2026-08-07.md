# `bin/simple fix` on `spipe_missing_docstrings` corrupts `describe "..."` string literals
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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


## Resolved 2026-11-25 — insertion-point logic verified correct at HEAD; regression spec added

Re-investigated on release/1.0.0 (Windows host, pinned seed v1.0.0-rc.1). The
corruption does NOT reproduce against the current fixer: driving
`check_spipe_missing_docstrings` (src/lib/nogc_sync_mut/tooling/easy_fix/
rules_lint.spl) plus the `FixApplicator` replacement pipeline
(easyfix_sort_replacements_descending + easyfix_apply_sorted_replacements)
over the exact repro shape from this doc produces a pure insertion at byte 33 —
immediately after the `describe "KernelSessionManager":\n` header — and the
applied output parses cleanly:

```
describe "KernelSessionManager":
    """
    ## KernelSessionManager

    Description of this describe block.
    """
    it "creates a session with a default mode":
        ...
```

A multi-block probe (comment header + a describe that already has a docstring
+ a bare describe + a bare context) is also correct: the documented block is
left untouched (0 fixes), the bare blocks get docstrings inserted after their
own headers, output intact. The insertion-point corruption described here was
evidently repaired by the intervening easy_fix consolidation/refactor commits
(the rule now lives in a single std-owned copy with i64 byte-offset helpers,
e.g. 49a297c305c / 6778d66d064).

Verification limit: `bin/simple fix` and `bin/simple test` cannot run on this
host because release/1.0.0 HEAD is source/binary inconsistent
(`unknown decorator '@representation_boundary'` in the lint_entry/test-runner
closures — known seed skew, not this defect). All evidence above comes from
standalone probes executing the REAL rule + applicator functions
(`SIMPLE_EXECUTION_MODE=interpreter`, rc=0), not from the full CLI.

Changes landed with this note:
- `test/01_unit/app/fix/lint_spec.spl`: repaired stale imports
  (`std.common.tooling.easy_fix.*` resolves to no module in the tree — the
  spec could not even load) to the real owners
  (`std.tooling.easy_fix.types` / `std.tooling.easy_fix.rules_lint`), and added
  two regression cases pinning the insertion byte offset (start == end == 33,
  prefix ends with the header + newline) and the has-docstring no-op case.
  Every `it` body in the file was re-verified green via the probe harness
  (t1..t6 all true).
