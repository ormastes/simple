# lifecycle_identity_spec

> Proves stable logical changes and immutable exact revisions for SCV lifecycle maintainers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# lifecycle_identity_spec

Proves stable logical changes and immutable exact revisions for SCV lifecycle maintainers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/scv/lifecycle_identity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Proves stable logical changes and immutable exact revisions for SCV lifecycle maintainers.

## Scenarios

### SCV lifecycle identity

#### keeps one logical change stable while revisions remain immutable

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps one logical change stable while revisions remain immutable
- Create one stable logical change
   - Expected: first.change_id equals `repeated.change_id`
- Derive immutable revisions from policy-significant content
   - Expected: lifecycle_validate_revision(revision_a).status equals `valid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps one logical change stable while revisions remain immutable")
step("Create one stable logical change")
val first = lifecycle_change_identity("seed-1", "Typed integration", "dev-infra", "one intent")
val repeated = lifecycle_change_identity("seed-1", "Typed integration", "dev-infra", "one intent")
expect(first.change_id).to_equal(repeated.change_id)

step("Derive immutable revisions from policy-significant content")
val aliases = lifecycle_aliases("jj-change", "jj-commit", "git-oid", ["github:42:sha"])
val revision_a = lifecycle_revision_identity(first.change_id, "tree-a", ["rev-parent"], "author=a", aliases)
val revision_b = lifecycle_revision_identity(first.change_id, "tree-b", ["rev-parent"], "author=a", aliases)
expect(revision_a.revision_id).to_start_with("rev_")
expect(revision_a.revision_id == revision_b.revision_id).to_be(false)
expect(lifecycle_validate_revision(revision_a).status).to_equal("valid")
```

</details>

#### rejects an unsafe tree identity

- rejects an unsafe tree identity
   - Expected: lifecycle_validate_revision(revision).code equals `LIFECYCLE_TREE_ID`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects an unsafe tree identity")
val change = lifecycle_change_identity("seed-2", "Unsafe tree", "dev-infra", "reject unsafe")
val revision = lifecycle_revision_identity(change.change_id, "", [], "", lifecycle_aliases("", "", "", []))
expect(lifecycle_validate_revision(revision).code).to_equal("LIFECYCLE_TREE_ID")
```

</details>

#### rejects aliases that cannot be independently mapped

- rejects aliases that cannot be independently mapped
   - Expected: lifecycle_aliases_validate(lifecycle_aliases("", "jj-commit", "abc", ["unqualified"])).code equals `LIFECYCLE_JJ_ALIAS`
   - Expected: lifecycle_aliases_validate(lifecycle_aliases("jj-change", "jj-commit", "abcdef1", ["github:42:sha"])).status equals `aliases_valid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects aliases that cannot be independently mapped")
expect(lifecycle_aliases_validate(lifecycle_aliases("", "jj-commit", "abc", ["unqualified"])).code).to_equal("LIFECYCLE_JJ_ALIAS")
expect(lifecycle_aliases_validate(lifecycle_aliases("jj-change", "jj-commit", "abcdef1", ["github:42:sha"])).status).to_equal("aliases_valid")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-001`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c48c34e156595ddb548cc0ce70d9faa517b55ee26c6467cc194f20e641d31008`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c48c34e156595ddb548cc0ce70d9faa517b55ee26c6467cc194f20e641d31008`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c48c34e156595ddb548cc0ce70d9faa517b55ee26c6467cc194f20e641d31008`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/scv/lifecycle_identity_spec.spl
mirror: doc/06_spec/01_unit/lib/scv/lifecycle_identity_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/scv/lifecycle_identity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/scv/lifecycle_identity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/scv/lifecycle_identity_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/scv/lifecycle_identity_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps one logical change stable while revisions remain immutable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/scv/lifecycle_identity_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an unsafe tree identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/scv/lifecycle_identity_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects aliases that cannot be independently mapped' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
