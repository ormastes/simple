# Extension Roots Specification

> Tests covering editor extension root policy.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Extension Roots Specification

## Scenarios

### editor extension root policy

#### keeps VS Code-like workspace roots in shared lib

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps VS Code-like workspace roots in shared lib
   - Expected: roots.len() equals `2`
   - Expected: roots[0] equals `.simple/editor/extensions`
   - Expected: roots[1] equals `.vscode/simple-editor/extensions`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps VS Code-like workspace roots in shared lib")
val roots = editor_extension_workspace_roots()
expect(roots.len()).to_equal(2)
expect(roots[0]).to_equal(".simple/editor/extensions")
expect(roots[1]).to_equal(".vscode/simple-editor/extensions")
```

</details>

#### merges configured, user, and system roots without runtime env access

- merges configured, user, and system roots without runtime env access
   - Expected: roots.len() equals `8`
   - Expected: roots[0] equals `.simple/editor/extensions`
   - Expected: roots[1] equals `.vscode/simple-editor/extensions`
   - Expected: roots[2] equals `/opt/a`
   - Expected: roots[3] equals `/opt/b`
   - Expected: roots[4] equals `/home/dev/.simple/editor/extensions`
   - Expected: roots[5] equals `/home/dev/.simple/extensions`
   - Expected: roots[6] equals `/usr/local/share/simple/editor/extensions`
   - Expected: roots[7] equals `/usr/share/simple/editor/extensions`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("merges configured, user, and system roots without runtime env access")
val roots = editor_extension_roots_from_inputs("/opt/a:/opt/b", "/home/dev")
expect(roots.len()).to_equal(8)
expect(roots[0]).to_equal(".simple/editor/extensions")
expect(roots[1]).to_equal(".vscode/simple-editor/extensions")
expect(roots[2]).to_equal("/opt/a")
expect(roots[3]).to_equal("/opt/b")
expect(roots[4]).to_equal("/home/dev/.simple/editor/extensions")
expect(roots[5]).to_equal("/home/dev/.simple/extensions")
expect(roots[6]).to_equal("/usr/local/share/simple/editor/extensions")
expect(roots[7]).to_equal("/usr/share/simple/editor/extensions")
```

</details>

#### omits user roots when home is unavailable

- omits user roots when home is unavailable
   - Expected: roots.len() equals `4`
   - Expected: roots[0] equals `.simple/editor/extensions`
   - Expected: roots[1] equals `.vscode/simple-editor/extensions`
   - Expected: roots[2] equals `/usr/local/share/simple/editor/extensions`
   - Expected: roots[3] equals `/usr/share/simple/editor/extensions`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("omits user roots when home is unavailable")
val roots = editor_extension_roots_from_inputs("", "")
expect(roots.len()).to_equal(4)
expect(roots[0]).to_equal(".simple/editor/extensions")
expect(roots[1]).to_equal(".vscode/simple-editor/extensions")
expect(roots[2]).to_equal("/usr/local/share/simple/editor/extensions")
expect(roots[3]).to_equal("/usr/share/simple/editor/extensions")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/editor/extension_roots_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering editor extension root policy.
- editor extension root policy

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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a6ee5855327d8d774672da8ca811841fdbdabdbca6cf93989372db687d095857`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a6ee5855327d8d774672da8ca811841fdbdabdbca6cf93989372db687d095857`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a6ee5855327d8d774672da8ca811841fdbdabdbca6cf93989372db687d095857`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/editor/extension_roots_spec.spl
mirror: doc/06_spec/unit/lib/editor/extension_roots_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/editor/extension_roots_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/editor/extension_roots_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/editor/extension_roots_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/editor/extension_roots_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps VS Code-like workspace roots in shared lib' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/editor/extension_roots_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'merges configured, user, and system roots without runtime env access' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/editor/extension_roots_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'omits user roots when home is unavailable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
