# Release Archive Layout

> Checks release workflow source resolves installed runtimes from the extracted

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Release Archive Layout

Checks release workflow source resolves installed runtimes from the extracted

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/release/release_archive_layout_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks release workflow source resolves installed runtimes from the extracted
archive root and reuses the declared bootstrap runtime and launcher for fallback.

## Scenarios

### release archive layout

#### should derive installer runtime paths from the extracted archive root

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should derive installer runtime paths from the extracted archive root
- Verify release archives expose the installed runtime layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should derive installer runtime paths from the extracted archive root")
step("Verify release archives expose the installed runtime layout")
val workflow = read_file_text(".github/workflows/release.yml") ?? ""

expect(workflow).to_contain("LINUX_PKG_ROOT=\"${LINUX_ARCHIVE%.spk}\"")
expect(workflow).to_contain("$LINUX_PKG_ROOT/bin/simple-runtime")
expect(workflow).to_contain("WINDOWS_PKG_ROOT=\"${WINDOWS_ARCHIVE%.spk}\"")
expect(workflow).to_contain("$WINDOWS_PKG_ROOT/bin/simple.exe")
expect(workflow.contains("if [ -f bin/simple-runtime ]; then")).to_be(false)
expect(workflow.contains("if [ -f bin/simple.exe ]; then")).to_be(false)
```

</details>

#### should reuse the bootstrap runtime and launcher in the full fallback

- should reuse the bootstrap runtime and launcher in the full fallback
- Verify release archives expose the installed runtime layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should reuse the bootstrap runtime and launcher in the full fallback")
step("Verify release archives expose the installed runtime layout")
val workflow = read_file_text(".github/workflows/release.yml") ?? ""

expect(workflow).to_contain("needs: [check-version, build-bootstrap]")
expect(workflow).to_contain("name: bootstrap-linux-x86_64")
expect(workflow).to_contain("FULL_BOOTSTRAP_ROOT=\"${FULL_ARCHIVE%.spk}\"")
expect(workflow).to_contain("test -x \"$FULL_BOOTSTRAP_ROOT/bin/simple-runtime\"")
expect(workflow).to_contain("test -x \"$FULL_BOOTSTRAP_ROOT/bin/simple\"")
expect(workflow).to_contain("cp \"$FULL_BOOTSTRAP_ROOT/bin/simple-runtime\" \"$PKG_ROOT/bin/\"")
expect(workflow).to_contain("cp \"$FULL_BOOTSTRAP_ROOT/bin/simple\" \"$PKG_ROOT/bin/\"")
expect(workflow).to_contain("dist/simple-full-*.tar.gz.sha256")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f3b8a74997fd8dbfc4c0a695f6e0b46f15b1cc49d891b709aec30689e85a873e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f3b8a74997fd8dbfc4c0a695f6e0b46f15b1cc49d891b709aec30689e85a873e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f3b8a74997fd8dbfc4c0a695f6e0b46f15b1cc49d891b709aec30689e85a873e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/release/release_archive_layout_spec.spl
mirror: doc/06_spec/01_unit/app/release/release_archive_layout_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/release/release_archive_layout_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/release/release_archive_layout_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/release/release_archive_layout_spec.spl:23:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should derive installer runtime paths from the extracted archive root' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/release/release_archive_layout_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should derive installer runtime paths from the extracted archive root' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/release/release_archive_layout_spec.spl:37:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reuse the bootstrap runtime and launcher in the full fallback' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/release/release_archive_layout_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reuse the bootstrap runtime and launcher in the full fallback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
