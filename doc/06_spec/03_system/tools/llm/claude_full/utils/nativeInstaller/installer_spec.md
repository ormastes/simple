# Claude Full Native Installer Slice

> Focused Simple coverage for native installer platform/path/binary helpers from

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Native Installer Slice

Focused Simple coverage for native installer platform/path/binary helpers from

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/nativeInstaller/installer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused Simple coverage for native installer platform/path/binary helpers from
utils/nativeInstaller/installer.ts.

## Scenarios

### Claude full native installer parity

#### should model platform and binary name helpers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should model platform and binary name helpers
- Check platform helpers
   - Expected: VERSION_RETENTION_COUNT equals `3`
   - Expected: getPlatformRoute("linux", "x64", false) equals `linux-x64`
   - Expected: getPlatformRoute("linux", "arm64", true) equals `linux-arm64-musl`
   - Expected: getPlatformRoute("plan9", "x64", false) equals `unsupported platform`
   - Expected: getBinaryNameRoute("win32-x64") equals `claude.exe`
   - Expected: getBinaryNameRoute("linux-x64") equals `claude`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model platform and binary name helpers")
step("Check platform helpers")
expect(VERSION_RETENTION_COUNT).to_equal(3)
expect(getPlatformRoute("linux", "x64", false)).to_equal("linux-x64")
expect(getPlatformRoute("linux", "arm64", true)).to_equal("linux-arm64-musl")
expect(getPlatformRoute("plan9", "x64", false)).to_equal("unsupported platform")
expect(getBinaryNameRoute("win32-x64")).to_equal("claude.exe")
expect(getBinaryNameRoute("linux-x64")).to_equal("claude")
```

</details>

#### should model base directory and binary checks

- should model base directory and binary checks
- Check path helpers
   - Expected: getBaseDirectoriesRoute("/xdg", "/bin") equals `/xdg/claude/versions|/xdg/claude/staging|/xdg/claude/locks|/bin/claude`
   - Expected: isPossibleClaudeBinaryRoute(false, 10, true) is false
   - Expected: isPossibleClaudeBinaryRoute(true, 0, true) is false
   - Expected: isPossibleClaudeBinaryRoute(true, 10, false) is false
   - Expected: isPossibleClaudeBinaryRoute(true, 10, true) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model base directory and binary checks")
step("Check path helpers")
expect(getBaseDirectoriesRoute("/xdg", "/bin")).to_equal("/xdg/claude/versions|/xdg/claude/staging|/xdg/claude/locks|/bin/claude")
expect(isPossibleClaudeBinaryRoute(false, 10, true)).to_equal(false)
expect(isPossibleClaudeBinaryRoute(true, 0, true)).to_equal(false)
expect(isPossibleClaudeBinaryRoute(true, 10, false)).to_equal(false)
expect(isPossibleClaudeBinaryRoute(true, 10, true)).to_equal(true)
```

</details>

#### should model version paths and empty dir cleanup

- should model version paths and empty dir cleanup
- Check version and cleanup routes
   - Expected: getVersionPathsRoute("/base", "1.2.3", true) equals `/base/versions/1.2.3|created-version-file|/base/staging/1.2.3`
   - Expected: getVersionPathsRoute("/base", "1.2.3", false) equals `/base/versions/1.2.3|version-file|/base/staging/1.2.3`
   - Expected: removeDirectoryIfEmptyRoute("", true) equals `removed`
   - Expected: removeDirectoryIfEmptyRoute("ENOENT", false) equals `ignored`
   - Expected: removeDirectoryIfEmptyRoute("ENOTDIR", false) equals `ignored`
   - Expected: removeDirectoryIfEmptyRoute("ENOTEMPTY", false) equals `ignored`
   - Expected: nativeInstallerSourceLinesModeled() equals `1708`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model version paths and empty dir cleanup")
step("Check version and cleanup routes")
expect(getVersionPathsRoute("/base", "1.2.3", true)).to_equal("/base/versions/1.2.3|created-version-file|/base/staging/1.2.3")
expect(getVersionPathsRoute("/base", "1.2.3", false)).to_equal("/base/versions/1.2.3|version-file|/base/staging/1.2.3")
expect(removeDirectoryIfEmptyRoute("", true)).to_equal("removed")
expect(removeDirectoryIfEmptyRoute("ENOENT", false)).to_equal("ignored")
expect(removeDirectoryIfEmptyRoute("ENOTDIR", false)).to_equal("ignored")
expect(removeDirectoryIfEmptyRoute("ENOTEMPTY", false)).to_equal("ignored")
expect(nativeInstallerSourceLinesModeled()).to_equal(1708)
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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4f0b2a9e1ab56a1a113b4a19d868c975530eb37e1648c06093162df6179f26ac`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4f0b2a9e1ab56a1a113b4a19d868c975530eb37e1648c06093162df6179f26ac`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4f0b2a9e1ab56a1a113b4a19d868c975530eb37e1648c06093162df6179f26ac`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/utils/nativeInstaller/installer_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/nativeInstaller/installer_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/nativeInstaller/installer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/nativeInstaller/installer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/nativeInstaller/installer_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/nativeInstaller/installer_spec.spl:19:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model platform and binary name helpers' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/nativeInstaller/installer_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model platform and binary name helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/nativeInstaller/installer_spec.spl:30:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model base directory and binary checks' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/nativeInstaller/installer_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model base directory and binary checks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/nativeInstaller/installer_spec.spl:40:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model version paths and empty dir cleanup' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/nativeInstaller/installer_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model version paths and empty dir cleanup' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
