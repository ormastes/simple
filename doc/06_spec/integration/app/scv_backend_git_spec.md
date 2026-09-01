# scv_backend_git_spec

> Purpose: This spec proves the read-only Git/jj sidecar backend adapter

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_backend_git_spec

Purpose: This spec proves the read-only Git/jj sidecar backend adapter

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_backend_git_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves the read-only Git/jj sidecar backend adapter
(`scv backend status|map|verify`, MIG-13): status reports git HEAD/branch and
jj presence without executing jj, map writes SCV<->git mapping rows to
`.scv/meta/backend_map.sdn`, and verify re-runs the byte-for-byte backend
comparison with a fail-closed verdict. Mutation of git refs is impossible by
construction: the adapter only shells read-only git queries.
Audience: Maintainers of the SCV migration tooling.

## Scenarios

### scv backend (read-only git/jj sidecar)

#### reports git HEAD and jj presence without executing jj

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports git HEAD and jj presence without executing jj
- Run backend status against a colocated git repo with a .jj dir
- Verify git and jj availability rows and the PASS verdict


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports git HEAD and jj presence without executing jj")
step("Run backend status against a colocated git repo with a .jj dir")
var lines = _prelude("status")
lines.push("REF=$(git rev-parse HEAD)")
lines.push("scv backend status --git .")
lines.push("printf 'be_code=%s\\n' \"$?\"")
lines.push("printf 'head=%s\\n' \"$REF\"")
val out = _run(lines)
step("Verify git and jj availability rows and the PASS verdict")
expect(out).to_contain("git: available head=")
expect(out).to_contain("jj: available (.jj present; probe only, never executed)")
expect(out).to_contain("PASS — backend status read, 0 mutations")
expect(out).to_contain("be_code=0")
```

</details>

#### maps SCV paths to git blobs in backend_map.sdn and verifies clean

- maps SCV paths to git blobs in backend_map.sdn and verifies clean
- Run backend map then verify; git refs must be untouched
- Verify mapping rows, PASS verdicts, and unchanged git HEAD


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("maps SCV paths to git blobs in backend_map.sdn and verifies clean")
step("Run backend map then verify; git refs must be untouched")
var lines = _prelude("map")
lines.push("BEFORE=$(git rev-parse HEAD)")
lines.push("scv backend map --git .")
lines.push("printf 'map_code=%s\\n' \"$?\"")
lines.push("echo '--- backend_map ---'")
lines.push("cat .scv/meta/backend_map.sdn")
lines.push("scv backend verify --git .")
lines.push("printf 'vf_code=%s\\n' \"$?\"")
lines.push("AFTER=$(git rev-parse HEAD)")
lines.push("test \"$BEFORE\" = \"$AFTER\" && echo refs_untouched=yes")
val out = _run(lines)
step("Verify mapping rows, PASS verdicts, and unchanged git HEAD")
expect(out).to_contain("PASS — 3 path(s) mapped, 0 unmapped")
expect(out).to_contain("scv_commit: commit_")
expect(out).to_contain("git_commit: ")
expect(out).to_contain("a.txt, sha256_")
expect(out).to_contain("sub/b.txt, sha256_")
expect(out).to_contain("PASS — 3 path(s) compared, 0 mismatches")
expect(out).to_contain("map_code=0")
expect(out).to_contain("vf_code=0")
expect(out).to_contain("refs_untouched=yes")
```

</details>

#### fails verify when the committed git content diverges

- fails verify when the committed git content diverges
- Commit a modified file in the git worktree and re-verify
- Verify the mismatch is named and the exit code is 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fails verify when the committed git content diverges")
step("Commit a modified file in the git worktree and re-verify")
var lines = _prelude("diverge")
lines.push("printf 'ALPHA\\n' > a.txt")
lines.push("git add -A")
lines.push("git -c user.email=t@t -c user.name=t commit -q -m diverge")
lines.push("git checkout -q HEAD~1 -- a.txt 2>/dev/null || true")
lines.push("set +e")
lines.push("scv backend verify --git .")
lines.push("printf 'vf_code=%s\\n' \"$?\"")
lines.push("set -e")
val out = _run(lines)
step("Verify the mismatch is named and the exit code is 1")
expect(out).to_contain("bytes differ: a.txt")
expect(out).to_contain("FAIL — 1 mismatch(es)")
expect(out).to_contain("vf_code=1")
```

</details>

#### errors read-only when no git repository is present

- errors read-only when no git repository is present
- Point backend status/map at a plain directory
- Verify the nothing-was-checked verdicts


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("errors read-only when no git repository is present")
step("Point backend status/map at a plain directory")
var lines = _prelude("nogit")
lines.push("mkdir \"$TMP/empty\"")
lines.push("set +e")
lines.push("scv backend status --git \"$TMP/empty\"")
lines.push("printf 'st_code=%s\\n' \"$?\"")
lines.push("scv backend map --git \"$TMP/empty\"")
lines.push("printf 'mp_code=%s\\n' \"$?\"")
lines.push("set -e")
val out = _run(lines)
step("Verify the nothing-was-checked verdicts")
expect(out).to_contain("ERROR — nothing was checked (no git repository at")
expect(out).to_contain("st_code=2")
expect(out).to_contain("mp_code=2")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-SCV-BACKEND-GIT-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a31a8d008a141c01da7c6dd228afff7639d399cb413b16a1d1fda736375786cc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a31a8d008a141c01da7c6dd228afff7639d399cb413b16a1d1fda736375786cc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a31a8d008a141c01da7c6dd228afff7639d399cb413b16a1d1fda736375786cc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/integration/app/scv_backend_git_spec.spl
mirror: doc/06_spec/integration/app/scv_backend_git_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/integration/app/scv_backend_git_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_backend_git_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_backend_git_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/integration/app/scv_backend_git_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports git HEAD and jj presence without executing jj' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_backend_git_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps SCV paths to git blobs in backend_map.sdn and verifies clean' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_backend_git_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails verify when the committed git content diverges' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
