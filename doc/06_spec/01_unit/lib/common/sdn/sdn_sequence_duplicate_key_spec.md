# sdn_sequence_duplicate_key_spec

> `parse_with_issues` reports a repeated mapping key so a strict consumer can refuse it. A block sequence writes the same key once per entry — `- name: a` then `- name: b` — and those are two different objects, not a repeated key. Reporting them as duplicates made every strict consumer refuse any multi-entry sequence.

<!-- sdn-diagram:id=sdn_sequence_duplicate_key_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sdn_sequence_duplicate_key_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sdn_sequence_duplicate_key_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sdn_sequence_duplicate_key_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sdn_sequence_duplicate_key_spec

`parse_with_issues` reports a repeated mapping key so a strict consumer can refuse it. A block sequence writes the same key once per entry — `- name: a` then `- name: b` — and those are two different objects, not a repeated key. Reporting them as duplicates made every strict consumer refuse any multi-entry sequence.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/lib/common/sdn/sdn_sequence_duplicate_key_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`parse_with_issues` reports a repeated mapping key so a strict consumer can
refuse it. A block sequence writes the same key once per entry — `- name: a`
then `- name: b` — and those are two different objects, not a repeated key.
Reporting them as duplicates made every strict consumer refuse any
multi-entry sequence.

## Examples

Regression + generalization for
`doc/08_tracking/bug/sdn_block_sequence_entries_reported_as_duplicate_keys_2026-09-07.md`.

## Scenarios

### SDN duplicate-key reporting across block sequences

#### reports no duplicate when each sequence entry repeats the same key

- Parse a four-entry sequence where every entry has name and ref
- Confirm the parse succeeded and reported nothing
   - Expected: kinds.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Parse a four-entry sequence where every entry has name and ref")
val src = "spec:\n" +
          "    jobs:\n" +
          "        - name: a\n" +
          "          ref: one\n" +
          "        - name: b\n" +
          "          ref: two\n" +
          "        - name: c\n" +
          "          ref: three\n" +
          "        - name: d\n" +
          "          ref: four\n"
val kinds = issue_kinds(src)

step("Confirm the parse succeeded and reported nothing")
expect(kinds.len()).to_equal(0)
```

</details>

#### still reports a key genuinely repeated inside one sequence entry

- Parse a sequence whose second entry declares ref twice
- Confirm exactly the in-entry repeat is reported
   - Expected: kinds.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Parse a sequence whose second entry declares ref twice")
val src = "spec:\n" +
          "    jobs:\n" +
          "        - name: a\n" +
          "          ref: one\n" +
          "        - name: b\n" +
          "          ref: two\n" +
          "          ref: three\n"
val kinds = issue_kinds(src)

step("Confirm exactly the in-entry repeat is reported")
expect(kinds.len()).to_equal(1)
expect(kinds[0]).to_start_with("duplicate_key@")
```

</details>

#### still reports a repeated key in an ordinary mapping

- Parse a mapping that declares name twice
- Confirm the repeat is reported at its own path
   - Expected: kinds.len() equals `1`
   - Expected: kinds[0] equals `duplicate_key@metadata.name`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Parse a mapping that declares name twice")
val src = "metadata:\n    name: one\n    ns: ci\n    name: two\n"
val kinds = issue_kinds(src)

step("Confirm the repeat is reported at its own path")
expect(kinds.len()).to_equal(1)
expect(kinds[0]).to_equal("duplicate_key@metadata.name")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

## Generation history

Generated by `simple spipe-docgen` (Simple).
Source SHA-256: `53d2fcc367c2985f83eb02027003256e15c7172705e0dbea557f529434fbbacd`
