# Claude Full keyboardShortcuts

> Pure Simple coverage for macOS Option-key shortcut mapping.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full keyboardShortcuts

Pure Simple coverage for macOS Option-key shortcut mapping.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/keyboard_shortcuts_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for macOS Option-key shortcut mapping.

## Scenarios

### Claude full keyboardShortcuts

#### maps macOS option special character source keys

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- maps macOS option special character source keys
- Check option key bindings
   - Expected: macosOptionSpecialCharBinding("dagger") equals `alt+t`
   - Expected: macosOptionSpecialCharBinding("pi") equals `alt+p`
   - Expected: macosOptionSpecialCharBinding("o-slash") equals `alt+o`
   - Expected: macosOptionSpecialCharBinding("x") equals ``
   - Expected: macosOptionSpecialCharBindingByCodepoint(0x2020) equals `alt+t`
   - Expected: macosOptionSpecialCharBindingByCodepoint(0x03c0) equals `alt+p`
   - Expected: macosOptionSpecialCharBindingByCodepoint(0x00f8) equals `alt+o`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps macOS option special character source keys")
step("Check option key bindings")
expect(macosOptionSpecialCharBinding("dagger")).to_equal("alt+t")
expect(macosOptionSpecialCharBinding("pi")).to_equal("alt+p")
expect(macosOptionSpecialCharBinding("o-slash")).to_equal("alt+o")
expect(macosOptionSpecialCharBinding("x")).to_equal("")
expect(macosOptionSpecialCharBindingByCodepoint(0x2020)).to_equal("alt+t")
expect(macosOptionSpecialCharBindingByCodepoint(0x03c0)).to_equal("alt+p")
expect(macosOptionSpecialCharBindingByCodepoint(0x00f8)).to_equal("alt+o")
```

</details>

#### detects mapped option special characters

- detects mapped option special characters
- Check type guard route
   - Expected: isMacosOptionChar("dagger") is true
   - Expected: isMacosOptionChar("pi") is true
   - Expected: isMacosOptionChar("o-slash") is true
   - Expected: isMacosOptionChar("plain") is false
   - Expected: isMacosOptionCodepoint(0x2020) is true
   - Expected: isMacosOptionCodepoint(0x61) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects mapped option special characters")
step("Check type guard route")
expect(isMacosOptionChar("dagger")).to_equal(true)
expect(isMacosOptionChar("pi")).to_equal(true)
expect(isMacosOptionChar("o-slash")).to_equal(true)
expect(isMacosOptionChar("plain")).to_equal(false)
expect(isMacosOptionCodepoint(0x2020)).to_equal(true)
expect(isMacosOptionCodepoint(0x61)).to_equal(false)
```

</details>

#### keeps the upstream map size stable

- keeps the upstream map size stable
- Check source key metadata
   - Expected: macosOptionSpecialCharCount() equals `3`
   - Expected: macosOptionSpecialCharSourceKeys() equals `["dagger", "pi", "o-slash"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps the upstream map size stable")
step("Check source key metadata")
expect(macosOptionSpecialCharCount()).to_equal(3)
expect(macosOptionSpecialCharSourceKeys()).to_equal(["dagger", "pi", "o-slash"])
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

- Canonical SPipe generation for source `f65229eeb2821c8d69ae8c53c47629bb3ec8d9b7178ae951b42e8e17aa2f613e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f65229eeb2821c8d69ae8c53c47629bb3ec8d9b7178ae951b42e8e17aa2f613e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f65229eeb2821c8d69ae8c53c47629bb3ec8d9b7178ae951b42e8e17aa2f613e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/tools/llm/claude_full/utils/keyboard_shortcuts_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/keyboard_shortcuts_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/keyboard_shortcuts_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/keyboard_shortcuts_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/keyboard_shortcuts_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/keyboard_shortcuts_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps macOS option special character source keys' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/keyboard_shortcuts_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects mapped option special characters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/keyboard_shortcuts_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the upstream map size stable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
