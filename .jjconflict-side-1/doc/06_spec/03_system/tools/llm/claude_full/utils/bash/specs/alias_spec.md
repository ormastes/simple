# Claude Full bash alias spec

> Pure Simple coverage for alias command metadata.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full bash alias spec

Pure Simple coverage for alias command metadata.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/bash/specs/alias_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for alias command metadata.

## Scenarios

### Claude full bash alias command spec

#### exposes alias command metadata

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- exposes alias command metadata
- Check command metadata
   - Expected: spec.name equals `alias`
   - Expected: spec.description equals `Create or list command aliases`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exposes alias command metadata")
step("Check command metadata")
val spec = aliasCommandSpec()
expect(spec.name).to_equal("alias")
expect(spec.description).to_equal("Create or list command aliases")
```

</details>

#### exposes optional variadic definition args

- exposes optional variadic definition args
- Check arg metadata
   - Expected: args.name equals `definition`
   - Expected: args.description equals `Alias definition in the form name=value`
   - Expected: args.isOptional equals `Some(true)`
   - Expected: args.isVariadic equals `Some(true)`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exposes optional variadic definition args")
step("Check arg metadata")
val spec = aliasCommandSpec()
if val args = spec.args:
    expect(args.name).to_equal("definition")
    expect(args.description).to_equal("Alias definition in the form name=value")
    expect(args.isOptional).to_equal(Some(true))
    expect(args.isVariadic).to_equal(Some(true))
    expect(args.isCommand).to_be_nil()
else:
    expect(false).to_equal(true)
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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c0ed4a52661b06a6b6bf6259a00f0b27a0fc12a8effaf0bb1639b1e0ed78c9ec`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c0ed4a52661b06a6b6bf6259a00f0b27a0fc12a8effaf0bb1639b1e0ed78c9ec`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c0ed4a52661b06a6b6bf6259a00f0b27a0fc12a8effaf0bb1639b1e0ed78c9ec`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/tools/llm/claude_full/utils/bash/specs/alias_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/bash/specs/alias_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/bash/specs/alias_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/bash/specs/alias_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/bash/specs/alias_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes alias command metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/bash/specs/alias_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes optional variadic definition args' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
