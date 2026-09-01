# scv_rebuild_db_spec

> Purpose: This spec proves `scv rebuild-db` (MIG-11, v2 final report §16.1):

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_rebuild_db_spec

Purpose: This spec proves `scv rebuild-db` (MIG-11, v2 final report §16.1):

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_rebuild_db_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves `scv rebuild-db` (MIG-11, v2 final report §16.1):
derived indexes/meta are a materialized view — after deleting the status index
and object index, `rebuild-db` reconstructs them from the immutable objects +
journal, `scv doctor` is PASS, and `scv fsck` output is unchanged from before
the deletion. Verdict is the last line, PASS/FAIL/ERROR convention.
Audience: Maintainers of the SCV storage layer.

## Scenarios

### scv rebuild-db

#### rebuilds deleted derived indexes from immutable objects, doctor PASS and fsck unchanged

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rebuilds deleted derived indexes from immutable objects, doctor PASS and fsck unchanged
- Snapshot, record fsck, delete derived files, rebuild, re-verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rebuilds deleted derived indexes from immutable objects, doctor PASS and fsck unchanged")
step("Snapshot, record fsck, delete derived files, rebuild, re-verify")
var lines = _harness()
lines.push("FSCK_BEFORE=$(scv fsck || true)")
lines.push("INDEX_BEFORE=$(cat .scv/meta/status_index.sdn)")
lines.push("rm -f .scv/meta/status_index.sdn .scv/meta/object_index.sdn")
lines.push("scv rebuild-db")
lines.push("printf 'rebuild_code=%s\\n' \"$?\"")
lines.push("INDEX_AFTER=$(cat .scv/meta/status_index.sdn)")
lines.push("test \"$INDEX_BEFORE\" = \"$INDEX_AFTER\" && printf 'index=identical\\n'")
lines.push("test -f .scv/meta/object_index.sdn && printf 'object_index=present\\n'")
lines.push("scv doctor")
lines.push("FSCK_AFTER=$(scv fsck || true)")
lines.push("test \"$FSCK_BEFORE\" = \"$FSCK_AFTER\" && printf 'fsck=unchanged\\n'")
val out = _run(lines)
expect(out).to_contain("rebuild_code=0")
expect(out).to_contain("index=identical")
expect(out).to_contain("object_index=present")
expect(out).to_contain("fsck=unchanged")
expect(out).to_contain("PASS — derived state rebuilt")
expect(out).to_contain("exit=0")
```

</details>

#### keeps the working copy usable after a rebuild

- keeps the working copy usable after a rebuild
- Rebuild, then status stays clean and a new snapshot lands


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps the working copy usable after a rebuild")
step("Rebuild, then status stays clean and a new snapshot lands")
var lines = _harness()
lines.push("rm -f .scv/meta/status_index.sdn .scv/meta/object_index.sdn")
lines.push("scv rebuild-db >/dev/null")
lines.push("scv status")
lines.push("printf 'edit\\n' > a.txt")
lines.push("scv snapshot | grep -c '^snapshot commit_'")
lines.push("printf 'usable=ok\\n'")
val out = _run(lines)
expect(out).to_contain("clean")
expect(out).to_contain("usable=ok")
expect(out).to_contain("exit=0")
```

</details>

#### refuses with ERROR outside an initialized repository

- refuses with ERROR outside an initialized repository
- Run rebuild-db in an empty directory, expect fail-closed ERROR


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("refuses with ERROR outside an initialized repository")
step("Run rebuild-db in an empty directory, expect fail-closed ERROR")
val lines = [
    "set -eu",
    "REPO=$(pwd)",
    "TMP=$(mktemp -d /tmp/scv-rebuild-empty.XXXXXX)",
    "scv() { SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" \"$@\"; }",
    "cd \"$TMP\"",
    "set +e",
    "scv rebuild-db",
    "printf 'code=%s\\n' \"$?\""
]
val out = _run(lines)
expect(out).to_contain("ERROR — nothing was checked")
expect(out).to_contain("code=2")
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

- `REQ-SSPEC-INTEGRATION`
- `REQ-SCV-REBUILD-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7356e858553b982572f455385e0a3818b0e2fef166ec93907c54d0105f893d0a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7356e858553b982572f455385e0a3818b0e2fef166ec93907c54d0105f893d0a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7356e858553b982572f455385e0a3818b0e2fef166ec93907c54d0105f893d0a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/integration/app/scv_rebuild_db_spec.spl
mirror: doc/06_spec/integration/app/scv_rebuild_db_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/integration/app/scv_rebuild_db_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_rebuild_db_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_rebuild_db_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/integration/app/scv_rebuild_db_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rebuilds deleted derived indexes from immutable objects, doctor PASS and fsck unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_rebuild_db_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the working copy usable after a rebuild' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_rebuild_db_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses with ERROR outside an initialized repository' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
