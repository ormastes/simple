# Claude Full Auth Portable

> Pure Simple coverage for authPortable utility parity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Auth Portable

Pure Simple coverage for authPortable utility parity.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/auth_portable_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for authPortable utility parity.

## Scenarios

### Claude full auth portable

#### keeps short API keys unchanged

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps short API keys unchanged
- Check short key
   - Expected: normalizeApiKeyForConfig("short-key") equals `short-key`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps short API keys unchanged")
step("Check short key")
expect(normalizeApiKeyForConfig("short-key")).to_equal("short-key")
```

</details>

#### keeps twenty-character API keys unchanged

- keeps twenty-character API keys unchanged
- Check exact length key
   - Expected: normalizeApiKeyForConfig("12345678901234567890") equals `12345678901234567890`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps twenty-character API keys unchanged")
step("Check exact length key")
expect(normalizeApiKeyForConfig("12345678901234567890")).to_equal("12345678901234567890")
```

</details>

#### keeps only the final twenty characters for longer API keys

- keeps only the final twenty characters for longer API keys
- Check long key
   - Expected: normalizeApiKeyForConfig("sk-ant-api03-abcdefghijklmnopqrstuvwxyz") equals `ghijklmnopqrstuvwxyz`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps only the final twenty characters for longer API keys")
step("Check long key")
expect(normalizeApiKeyForConfig("sk-ant-api03-abcdefghijklmnopqrstuvwxyz")).to_equal("ghijklmnopqrstuvwxyz")
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

- Canonical SPipe generation for source `99cfc0784b5a4dade6a0cf9f990ddd17ff86dce38dd7686de42cb638caa7ab3a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `99cfc0784b5a4dade6a0cf9f990ddd17ff86dce38dd7686de42cb638caa7ab3a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `99cfc0784b5a4dade6a0cf9f990ddd17ff86dce38dd7686de42cb638caa7ab3a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/utils/auth_portable_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/auth_portable_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/auth_portable_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/auth_portable_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/auth_portable_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps short API keys unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/auth_portable_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps twenty-character API keys unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/auth_portable_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps only the final twenty characters for longer API keys' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
