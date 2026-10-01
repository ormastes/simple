# Claude Full crypto utils

> Pure Simple coverage for crypto.ts binding indirection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full crypto utils

Pure Simple coverage for crypto.ts binding indirection.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/crypto_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for crypto.ts binding indirection.

## Scenarios

### Claude full crypto utils

#### models the randomUUID binding seam

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- models the randomUUID binding seam
- Check import/export strategy
   - Expected: randomUUIDBindingName() equals `randomUUID`
   - Expected: cryptoImportStrategy() equals `explicit import then export`
   - Expected: cryptoBytecodeCompatible() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("models the randomUUID binding seam")
step("Check import/export strategy")
expect(randomUUIDBindingName()).to_equal("randomUUID")
expect(cryptoImportStrategy()).to_equal("explicit import then export")
expect(cryptoBytecodeCompatible()).to_equal(true)
```

</details>

#### models the browser build swap rationale

- models the browser build swap rationale
- Check browser target metadata
   - Expected: cryptoBrowserSwapTarget() equals `crypto.browser.ts`
   - Expected: cryptoAvoidedPolyfill() equals `crypto-browserify`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("models the browser build swap rationale")
step("Check browser target metadata")
expect(cryptoBrowserSwapTarget()).to_equal("crypto.browser.ts")
expect(cryptoAvoidedPolyfill()).to_equal("crypto-browserify")
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

- Canonical SPipe generation for source `b5f85cc81eeb12e6fe25651504d6bd51353643108088050702982ce8b7f5707b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b5f85cc81eeb12e6fe25651504d6bd51353643108088050702982ce8b7f5707b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b5f85cc81eeb12e6fe25651504d6bd51353643108088050702982ce8b7f5707b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/tools/llm/claude_full/utils/crypto_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/crypto_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/crypto_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/crypto_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/crypto_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'models the randomUUID binding seam' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/crypto_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'models the browser build swap rationale' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
