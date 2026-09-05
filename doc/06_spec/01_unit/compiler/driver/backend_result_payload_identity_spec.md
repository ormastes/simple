# Backend result payload identity

> The driver facade must expose backend result variants with the payload types

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend result payload identity

The driver facade must expose backend result variants with the payload types

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/backend_result_payload_identity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

The driver facade must expose backend result variants with the payload types
owned by `compiler.backend.backend_types`. Canonical configuration SDN values
remain a distinct type even though both domains represent SDN data.

## Scenarios

### driver backend result payload identity

#### keeps backend SDN payloads distinct from canonical configuration SDN

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps backend SDN payloads distinct from canonical configuration SDN


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps backend SDN payloads distinct from canonical configuration SDN")
val backend_value = BackendSdnValue.int(7)
val result = BackendResult.SdnData(backend_value)
match result:
    case BackendResult.SdnData(data):
        match data.kind:
            case SdnValueKind.Int(value): expect(value).to_equal(7)
            case _: expect("backend-int").to_equal("unexpected-kind")
    case _: expect("sdn-data").to_equal("unexpected-result")

val config_value = SdnValue.Int(9)
match config_value:
    case SdnValue.Int(value): expect(value).to_equal(9)
    case _: expect("config-int").to_equal("unexpected-kind")
```

</details>

#### keeps compiled-unit payloads bound to the backend owner

- keeps compiled-unit payloads bound to the backend owner
   - Expected: compiled.name equals `identity-probe`
   - Expected: compiled.code.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps compiled-unit payloads bound to the backend owner")
val unit = CompiledUnit(
    name: "identity-probe",
    code: [],
    symbols: {},
    entry_point: nil,
    relocations: []
)
val result = BackendResult.CompiledUnit(unit)
match result:
    case BackendResult.CompiledUnit(compiled):
        expect(compiled.name).to_equal("identity-probe")
        expect(compiled.code.len()).to_equal(0)
    case _: expect("compiled-unit").to_equal("unexpected-result")
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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6bbdf09cbc2f1dd5504cebbf1d406b29701335865bbd239649f6b9f4ecdbfbc2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6bbdf09cbc2f1dd5504cebbf1d406b29701335865bbd239649f6b9f4ecdbfbc2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6bbdf09cbc2f1dd5504cebbf1d406b29701335865bbd239649f6b9f4ecdbfbc2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/driver/backend_result_payload_identity_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/backend_result_payload_identity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver/backend_result_payload_identity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/backend_result_payload_identity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/backend_result_payload_identity_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/driver/backend_result_payload_identity_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps backend SDN payloads distinct from canonical configuration SDN' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/backend_result_payload_identity_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps compiled-unit payloads bound to the backend owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
