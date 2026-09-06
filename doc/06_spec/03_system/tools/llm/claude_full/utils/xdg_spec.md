# Claude Full XDG utils

> Pure Simple coverage for XDG directory resolution.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full XDG utils

Pure Simple coverage for XDG directory resolution.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/xdg_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for XDG directory resolution.

## Scenarios

### Claude full XDG utils

#### uses XDG env overrides when present

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses XDG env overrides when present
- Check env override values
   - Expected: getXDGStateHome(options) equals `/state`
   - Expected: getXDGCacheHome(options) equals `/cache`
   - Expected: getXDGDataHome(options) equals `/data`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses XDG env overrides when present")
step("Check env override values")
val options = XDGOptions(stateHome: Some("/state"), cacheHome: Some("/cache"), dataHome: Some("/data"), home: "/home/alice")
expect(getXDGStateHome(options)).to_equal("/state")
expect(getXDGCacheHome(options)).to_equal("/cache")
expect(getXDGDataHome(options)).to_equal("/data")
```

</details>

#### falls back to home-relative XDG defaults

- falls back to home-relative XDG defaults
- Check default paths
   - Expected: getXDGStateHome(options) equals `/home/alice/.local/state`
   - Expected: getXDGCacheHome(options) equals `/home/alice/.cache`
   - Expected: getXDGDataHome(options) equals `/home/alice/.local/share`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("falls back to home-relative XDG defaults")
step("Check default paths")
val options = XDGOptions(stateHome: nil, cacheHome: nil, dataHome: nil, home: "/home/alice")
expect(getXDGStateHome(options)).to_equal("/home/alice/.local/state")
expect(getXDGCacheHome(options)).to_equal("/home/alice/.cache")
expect(getXDGDataHome(options)).to_equal("/home/alice/.local/share")
```

</details>

#### resolves user bin from home

- resolves user bin from home
- Check user bin path
   - Expected: getUserBinDir(options) equals `/home/alice/.local/bin`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("resolves user bin from home")
step("Check user bin path")
val options = XDGOptions(stateHome: Some("/state"), cacheHome: Some("/cache"), dataHome: Some("/data"), home: "/home/alice")
expect(getUserBinDir(options)).to_equal("/home/alice/.local/bin")
```

</details>

#### does not duplicate a trailing home slash

- does not duplicate a trailing home slash
- Check slash join
   - Expected: getXDGCacheHome(options) equals `/home/alice/.cache`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not duplicate a trailing home slash")
step("Check slash join")
val options = XDGOptions(stateHome: nil, cacheHome: nil, dataHome: nil, home: "/home/alice/")
expect(getXDGCacheHome(options)).to_equal("/home/alice/.cache")
```

</details>

#### preserves explicitly empty XDG env overrides

- preserves explicitly empty XDG env overrides
- Check empty env override parity
   - Expected: getXDGStateHome(options) equals ``
   - Expected: getXDGCacheHome(options) equals ``
   - Expected: getXDGDataHome(options) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves explicitly empty XDG env overrides")
step("Check empty env override parity")
val options = XDGOptions(stateHome: Some(""), cacheHome: Some(""), dataHome: Some(""), home: "/home/alice")
expect(getXDGStateHome(options)).to_equal("")
expect(getXDGCacheHome(options)).to_equal("")
expect(getXDGDataHome(options)).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `cb6496cabf98d3b03064118279cebdfe69a216c9eef24447992fa6a198c37d7f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cb6496cabf98d3b03064118279cebdfe69a216c9eef24447992fa6a198c37d7f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cb6496cabf98d3b03064118279cebdfe69a216c9eef24447992fa6a198c37d7f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/utils/xdg_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/xdg_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/xdg_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/xdg_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/xdg_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses XDG env overrides when present' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/xdg_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'falls back to home-relative XDG defaults' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/xdg_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves user bin from home' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
