# Claude Full bash nohup spec

> Pure Simple coverage for nohup command metadata.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full bash nohup spec

Pure Simple coverage for nohup command metadata.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/bash/specs/nohup_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for nohup command metadata.

## Scenarios

### Claude full bash nohup command spec

#### exposes nohup command metadata

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- exposes nohup command metadata
- Check command metadata
   - Expected: spec.name equals `nohup`
   - Expected: spec.description equals `Run a command immune to hangups`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exposes nohup command metadata")
step("Check command metadata")
val spec = nohupCommandSpec()
expect(spec.name).to_equal("nohup")
expect(spec.description).to_equal("Run a command immune to hangups")
```

</details>

#### exposes command args

- exposes command args
- Check arg metadata
   - Expected: args.name equals `command`
   - Expected: args.description equals `Command to run with nohup`
   - Expected: args.isCommand equals `Some(true)`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exposes command args")
step("Check arg metadata")
val spec = nohupCommandSpec()
if val args = spec.args:
    expect(args.name).to_equal("command")
    expect(args.description).to_equal("Command to run with nohup")
    expect(args.isOptional).to_be_nil()
    expect(args.isVariadic).to_be_nil()
    expect(args.isCommand).to_equal(Some(true))
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

- Canonical SPipe generation for source `13a1ff7ffed83511bcfdb5b1193304cf53fa3796b994afc45dfd00723e3d83f4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `13a1ff7ffed83511bcfdb5b1193304cf53fa3796b994afc45dfd00723e3d83f4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `13a1ff7ffed83511bcfdb5b1193304cf53fa3796b994afc45dfd00723e3d83f4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/tools/llm/claude_full/utils/bash/specs/nohup_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/bash/specs/nohup_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/bash/specs/nohup_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/bash/specs/nohup_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/bash/specs/nohup_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes nohup command metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/bash/specs/nohup_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes command args' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
