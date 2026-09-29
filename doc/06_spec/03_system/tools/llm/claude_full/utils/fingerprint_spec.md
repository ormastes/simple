# Claude Full Fingerprint

> Pure Simple coverage for Claude Code fingerprint computation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Fingerprint

Pure Simple coverage for Claude Code fingerprint computation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/fingerprint_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for Claude Code fingerprint computation.

## Scenarios

### Claude full fingerprint parity

#### computes the salted three-character SHA-256 prefix

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- computes the salted three-character SHA-256 prefix
- Check indexed character hash
   - Expected: computeFingerprint("abcdefghijklmnopqrstuvwxyz", "1.2.3") equals `897`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("computes the salted three-character SHA-256 prefix")
step("Check indexed character hash")
expect(computeFingerprint("abcdefghijklmnopqrstuvwxyz", "1.2.3")).to_equal("897")
```

</details>

#### uses zero for missing indexed characters

- uses zero for missing indexed characters
- Check short message fallback
   - Expected: computeFingerprint("abc", "1.2.3") equals `ec7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses zero for missing indexed characters")
step("Check short message fallback")
expect(computeFingerprint("abc", "1.2.3")).to_equal("ec7")
```

</details>

#### indexes BMP unicode like JavaScript UTF-16 strings

- indexes BMP unicode like JavaScript UTF-16 strings
- Check BMP code unit indexing
   - Expected: computeFingerprint("abcdéfgHIJKLMNOPQRSTU", "1.2.3") equals `8c8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("indexes BMP unicode like JavaScript UTF-16 strings")
step("Check BMP code unit indexing")
expect(computeFingerprint("abcdéfgHIJKLMNOPQRSTU", "1.2.3")).to_equal("8c8")
```

</details>

#### hashes surrogate pair halves as replacement characters

- hashes surrogate pair halves as replacement characters
- Check astral code unit indexing
   - Expected: computeFingerprint("abcd😀fgHIJKLMNOPQRSTU", "1.2.3") equals `4b1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("hashes surrogate pair halves as replacement characters")
step("Check astral code unit indexing")
expect(computeFingerprint("abcd😀fgHIJKLMNOPQRSTU", "1.2.3")).to_equal("4b1")
```

</details>

#### extracts first user string content

- extracts first user string content
- Check first user message
   - Expected: extractFirstMessageText(messages) equals `hello world`
   - Expected: computeFingerprintFromMessages(messages, "1.2.3") equals `c30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("extracts first user string content")
step("Check first user message")
val messages = [
    FingerprintMessage(messageType: "assistant", stringContent: Some("skip"), textBlocks: []),
    FingerprintMessage(messageType: "user", stringContent: Some("hello world"), textBlocks: [])
]
expect(extractFirstMessageText(messages)).to_equal("hello world")
expect(computeFingerprintFromMessages(messages, "1.2.3")).to_equal("c30")
```

</details>

#### extracts first text block content

- extracts first text block content
- Check block content fallback
   - Expected: extractFirstMessageText(messages) equals `block text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("extracts first text block content")
step("Check block content fallback")
val messages = [FingerprintMessage(messageType: "user", stringContent: nil, textBlocks: ["block text", "later"])]
expect(extractFirstMessageText(messages)).to_equal("block text")
```

</details>

#### preserves empty string content before text blocks

- preserves empty string content before text blocks
- Check empty string content precedence
   - Expected: extractFirstMessageText(messages) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves empty string content before text blocks")
step("Check empty string content precedence")
val messages = [FingerprintMessage(messageType: "user", stringContent: Some(""), textBlocks: ["block text"])]
expect(extractFirstMessageText(messages)).to_equal("")
```

</details>

#### returns empty text when no user content exists

- returns empty text when no user content exists
- Check empty fallback
   - Expected: extractFirstMessageText(messages) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns empty text when no user content exists")
step("Check empty fallback")
val messages = [FingerprintMessage(messageType: "assistant", stringContent: Some("skip"), textBlocks: [])]
expect(extractFirstMessageText(messages)).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `34f3fe5b00570750e461af8688129e4109199cc0e6e29832c772c2c2516bdde4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `34f3fe5b00570750e461af8688129e4109199cc0e6e29832c772c2c2516bdde4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `34f3fe5b00570750e461af8688129e4109199cc0e6e29832c772c2c2516bdde4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/utils/fingerprint_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/fingerprint_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/fingerprint_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/fingerprint_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/fingerprint_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes the salted three-character SHA-256 prefix' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/fingerprint_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses zero for missing indexed characters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/fingerprint_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'indexes BMP unicode like JavaScript UTF-16 strings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
