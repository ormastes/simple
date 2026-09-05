# Claude Full Memory Versions

> Pure Simple coverage for `projectIsInGitRepo` parity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Memory Versions

Pure Simple coverage for `projectIsInGitRepo` parity.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/memory/versions_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for `projectIsInGitRepo` parity.

## Scenarios

### Claude full memory versions parity

#### detects a git marker at the starting directory

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- detects a git marker at the starting directory
- Check direct git marker
   - Expected: projectIsInGitRepoWithMarker("/repo", fakeGitMarker) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects a git marker at the starting directory")
step("Check direct git marker")
expect(projectIsInGitRepoWithMarker("/repo", fakeGitMarker)).to_equal(true)
```

</details>

#### walks parent directories until a git marker is found

- walks parent directories until a git marker is found
- Check parent git marker
   - Expected: projectIsInGitRepoWithMarker("/repo/a/b", fakeGitMarker) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("walks parent directories until a git marker is found")
step("Check parent git marker")
expect(projectIsInGitRepoWithMarker("/repo/a/b", fakeGitMarker)).to_equal(true)
```

</details>

#### returns false when no parent contains a git marker

- returns false when no parent contains a git marker
- Check missing git marker
   - Expected: projectIsInGitRepoWithMarker("/tmp/a/b", fakeGitMarker) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns false when no parent contains a git marker")
step("Check missing git marker")
expect(projectIsInGitRepoWithMarker("/tmp/a/b", fakeGitMarker)).to_equal(false)
```

</details>

#### normalizes slashes before walking

- normalizes slashes before walking
- Check slash normalization
   - Expected: projectIsInGitRepoWithMarker("/repo/a/b/", fakeGitMarker) is true
   - Expected: projectIsInGitRepoWithMarker("C:\\repo\\sub", fakeGitMarker) is true
   - Expected: projectIsInGitRepoFrom("relative\\child", "/home/me", fakeGitMarker) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("normalizes slashes before walking")
step("Check slash normalization")
expect(projectIsInGitRepoWithMarker("/repo/a/b/", fakeGitMarker)).to_equal(true)
expect(projectIsInGitRepoWithMarker("C:\\repo\\sub", fakeGitMarker)).to_equal(true)
expect(projectIsInGitRepoFrom("relative\\child", "/home/me", fakeGitMarker)).to_equal(true)
```

</details>

#### resolves dot segments before walking

- resolves dot segments before walking
- Check resolved dot segments
   - Expected: projectIsInGitRepoFrom("./relative/child", "/home/me/project/..", fakeGitMarker) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("resolves dot segments before walking")
step("Check resolved dot segments")
expect(projectIsInGitRepoFrom("./relative/child", "/home/me/project/..", fakeGitMarker)).to_equal(true)
```

</details>

#### stops correctly at filesystem roots

- stops correctly at filesystem roots
- Check root handling
   - Expected: projectIsInGitRepoWithMarker("/", fakeGitMarker) is false
   - Expected: projectIsInGitRepoWithMarker("C:/", fakeGitMarker) is true
   - Expected: projectIsInGitRepoWithMarker("C:/repo/sub", fakeGitMarker) is true
   - Expected: projectIsInGitRepoWithMarker("D:/tmp/sub", fakeGitMarker) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stops correctly at filesystem roots")
step("Check root handling")
expect(projectIsInGitRepoWithMarker("/", fakeGitMarker)).to_equal(false)
expect(projectIsInGitRepoWithMarker("C:/", fakeGitMarker)).to_equal(true)
expect(projectIsInGitRepoWithMarker("C:/repo/sub", fakeGitMarker)).to_equal(true)
expect(projectIsInGitRepoWithMarker("D:/tmp/sub", fakeGitMarker)).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `94dd725d5f4a429b1f384c3fb84aaf959cb2e48a7314d556f758da7ae5c946a0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `94dd725d5f4a429b1f384c3fb84aaf959cb2e48a7314d556f758da7ae5c946a0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `94dd725d5f4a429b1f384c3fb84aaf959cb2e48a7314d556f758da7ae5c946a0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/utils/memory/versions_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/memory/versions_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/memory/versions_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/memory/versions_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/memory/versions_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects a git marker at the starting directory' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/memory/versions_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'walks parent directories until a git marker is found' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/memory/versions_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns false when no parent contains a git marker' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
