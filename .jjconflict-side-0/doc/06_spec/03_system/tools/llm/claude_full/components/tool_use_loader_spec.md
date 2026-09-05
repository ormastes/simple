# Claude Full ToolUseLoader

> Pure Simple/TUI-compatible loader state model.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full ToolUseLoader

Pure Simple/TUI-compatible loader state model.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/tool_use_loader_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple/TUI-compatible loader state model.

## Scenarios

### Claude full ToolUseLoader

#### dims unresolved loader states

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- dims unresolved loader states
- Check unresolved animation visibility
   - Expected: hidden.glyph equals ` `
   - Expected: hidden.color equals ``
   - Expected: hidden.dim is true
   - Expected: visible.glyph equals `o`
   - Expected: visible.dim is true
   - Expected: useBlink(true, true) is true
   - Expected: useBlink(false, true) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("dims unresolved loader states")
step("Check unresolved animation visibility")
val hidden = ToolUseLoader(false, true, true, false)
expect(hidden.glyph).to_equal(" ")
expect(hidden.color).to_equal("")
expect(hidden.dim).to_equal(true)
val visible = ToolUseLoader(false, true, true, true)
expect(visible.glyph).to_equal("o")
expect(visible.dim).to_equal(true)
expect(useBlink(true, true)).to_equal(true)
expect(useBlink(false, true)).to_equal(false)
```

</details>

#### colors resolved loader states

- colors resolved loader states
- Check success and error colors
   - Expected: success.glyph equals `o`
   - Expected: success.color equals `success`
   - Expected: success.dim is false
   - Expected: error.color equals `error`
   - Expected: error.glyph equals `o`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("colors resolved loader states")
step("Check success and error colors")
val success = ToolUseLoader(false, false, true, false)
expect(success.glyph).to_equal("o")
expect(success.color).to_equal("success")
expect(success.dim).to_equal(false)
val error = ToolUseLoader(true, false, true, false)
expect(error.color).to_equal("error")
expect(error.glyph).to_equal("o")
```

</details>

#### keeps source layout and glyph metadata

- keeps source layout and glyph metadata
- Check stable TUI metadata
   - Expected: view.glyph equals `o`
   - Expected: view.minWidth equals `2`
   - Expected: view.sourceGlyph equals `BLACK_CIRCLE`
   - Expected: blackCircleGlyph("darwin") equals `darwin-black-circle`
   - Expected: blackCircleGlyph("linux") equals `black-circle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps source layout and glyph metadata")
step("Check stable TUI metadata")
val view = ToolUseLoader(false, true, false, false)
expect(view.glyph).to_equal("o")
expect(view.minWidth).to_equal(2)
expect(view.sourceGlyph).to_equal("BLACK_CIRCLE")
expect(blackCircleGlyph("darwin")).to_equal("darwin-black-circle")
expect(blackCircleGlyph("linux")).to_equal("black-circle")
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

- Canonical SPipe generation for source `33cd77aaa183ac3426e53c5fe1417234440735b6b8056a97f4e59db38fd4b876`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `33cd77aaa183ac3426e53c5fe1417234440735b6b8056a97f4e59db38fd4b876`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `33cd77aaa183ac3426e53c5fe1417234440735b6b8056a97f4e59db38fd4b876`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/tools/llm/claude_full/components/tool_use_loader_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/components/tool_use_loader_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/components/tool_use_loader_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/components/tool_use_loader_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/components/tool_use_loader_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/components/tool_use_loader_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dims unresolved loader states' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/tool_use_loader_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'colors resolved loader states' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/tool_use_loader_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps source layout and glyph metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
