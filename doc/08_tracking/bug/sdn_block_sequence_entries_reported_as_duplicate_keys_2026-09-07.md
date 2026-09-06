# SDN block-sequence entries were reported as duplicate keys

Date: 2026-09-07
Severity: HIGH (made every strict SDN consumer refuse any multi-entry block sequence)
Status: FIXED 2026-09-07
Binary: `bin/release/aarch64-unknown-linux-gnu/simple` (Rust seed, 50093192 bytes, mtime 2026-09-06 09:59:11)

## Symptom

`parse_with_issues` / `parse_with_spans_and_issues` reported a `duplicate_key`
issue for the repeated key of a block SEQUENCE, where each `- ` line starts a new
entry and repeating the key is the normal shape of a list:

```sdn
spec:
    jobs:
        - name: build-linux
          jobTemplateRef: echo-linux
        - name: build-probe
          jobTemplateRef: echo-probe
```

Observed: `duplicate_key @ spec.jobs.- name :: duplicate key '- name'`. Note the
key text — `- name`, with the sequence marker glued on — which is itself the
tell.

`parse` was unaffected (the value decoded correctly); only the issue list was
wrong. But any consumer that treats "an issue" as "refuse the document" — which
is exactly what a strict profile must do — rejected every pipeline, every
multi-container pod, every multi-entry list in the tree. Found while decoding a
four-job CI pipeline.

## Cause

`_sdn_issue_block` (`src/lib/common/sdn/parser.spl`) walked lines at one
indentation level accumulating a `seen` key list, and treated a `- name: x`
line as an ordinary mapping line: it never recognised the sequence marker, so
(a) the key it recorded included the `- ` prefix and (b) every entry shared one
key scope.

## Fix

In `_sdn_issue_block`, a line whose trimmed form starts with `- ` opens a new
sequence entry: reset `seen` and strip the marker before reading the key. Four
lines. `parse` behaviour is untouched — the issue collector is documented as
never changing it.

## Specs

`test/01_unit/lib/common/sdn/sdn_sequence_duplicate_key_spec.spl`

- reproducing: a four-entry sequence repeating `name`/`ref` reports 0 issues;
- generalizing: a key repeated INSIDE one entry is still reported (the fix must
  not blind the check), and a repeat in an ordinary mapping still reports at its
  own path.

Verified by reverting the fix: `3 total, 1 passed, 2 failed` — the reproducing
and in-entry examples both go red, the ordinary-mapping example stays green,
confirming the fix is scoped. Restored byte-identical, `3 total, 3 passed`.

No regressions in the neighbouring suites:
`sdn_spans_spec.spl` 16/16, `sdn/sdn_block_sequence_spec.spl` 7/7.

## Remaining limitation (deliberately not fixed here)

The issue path for a key inside a sequence entry is not index-qualified: it
reads `spec.jobs.ref` rather than `spec.jobs.1.ref`. Duplicate detection is now
correct; only the reported path is coarse. Index tracking in the issue walker is
a separate change with no consumer today.
