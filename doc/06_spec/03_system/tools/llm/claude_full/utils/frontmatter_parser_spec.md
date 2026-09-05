# Claude Full frontmatter parser helpers

> Pure Simple coverage for small frontmatter helper parity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full frontmatter parser helpers

Pure Simple coverage for small frontmatter helper parity.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/frontmatter_parser_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for small frontmatter helper parity.

## Scenarios

### Claude full frontmatter parser helpers

#### splits comma paths while respecting brace groups

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- splits comma paths while respecting brace groups
- Check brace-aware split
   - Expected: paths.len() equals `4`
   - Expected: paths[0] equals `a`
   - Expected: paths[1] equals `src/*.ts`
   - Expected: paths[2] equals `src/*.tsx`
   - Expected: paths[3] equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("splits comma paths while respecting brace groups")
step("Check brace-aware split")
val paths = splitPathInFrontmatter("a, src/*.{ts,tsx}, b")
expect(paths.len()).to_equal(4)
expect(paths[0]).to_equal("a")
expect(paths[1]).to_equal("src/*.ts")
expect(paths[2]).to_equal("src/*.tsx")
expect(paths[3]).to_equal("b")
```

</details>

#### expands nested brace alternatives

- expands nested brace alternatives
- Check recursive brace expansion
   - Expected: paths.len() equals `4`
   - Expected: paths[0] equals `a/c`
   - Expected: paths[3] equals `b/d`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("expands nested brace alternatives")
step("Check recursive brace expansion")
val paths = splitPathInFrontmatter("{a,b}/{c,d}")
expect(paths.len()).to_equal(4)
expect(paths[0]).to_equal("a/c")
expect(paths[3]).to_equal("b/d")
```

</details>

#### flattens path lists

- flattens path lists
- Check list input helper
   - Expected: paths.len() equals `3`
   - Expected: paths[2] equals `src/*.md`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("flattens path lists")
step("Check list input helper")
val paths = splitPathListInFrontmatter(["a", "src/*.{spl,md}"])
expect(paths.len()).to_equal(3)
expect(paths[2]).to_equal("src/*.md")
```

</details>

#### parses positive integer text

- parses positive integer text
- Check positive int parser
   - Expected: parsePositiveIntFromFrontmatter(FrontmatterValue.textValue("42")) equals `42`
   - Expected: parsePositiveIntFromFrontmatter(FrontmatterValue.textValue("42x")) equals `42`
   - Expected: parsePositiveIntFromFrontmatter(FrontmatterValue.intValue(7)) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses positive integer text")
step("Check positive int parser")
expect(parsePositiveIntFromFrontmatter(FrontmatterValue.textValue("42"))).to_equal(42)
expect(parsePositiveIntFromFrontmatter(FrontmatterValue.textValue("42x"))).to_equal(42)
expect(parsePositiveIntFromFrontmatter(FrontmatterValue.intValue(7))).to_equal(7)
expect(parsePositiveIntFromFrontmatter(FrontmatterValue.textValue("0"))).to_be_nil()
expect(parsePositiveIntFromFrontmatter(FrontmatterValue.textValue("x"))).to_be_nil()
```

</details>

#### parses boolean and shell frontmatter text

- parses boolean and shell frontmatter text
- Check scalar parsers
   - Expected: parseBooleanFrontmatter(FrontmatterValue.textValue("true")) is true
   - Expected: parseBooleanFrontmatter(FrontmatterValue.boolValue(true)) is true
   - Expected: parseBooleanFrontmatter(FrontmatterValue.textValue("TRUE")) is false
   - Expected: parseShellFrontmatter(FrontmatterValue.textValue(" PowerShell ")) equals `powershell`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses boolean and shell frontmatter text")
step("Check scalar parsers")
expect(parseBooleanFrontmatter(FrontmatterValue.textValue("true"))).to_equal(true)
expect(parseBooleanFrontmatter(FrontmatterValue.boolValue(true))).to_equal(true)
expect(parseBooleanFrontmatter(FrontmatterValue.textValue("TRUE"))).to_equal(false)
expect(parseShellFrontmatter(FrontmatterValue.textValue(" PowerShell "))).to_equal("powershell")
expect(parseShellFrontmatter(FrontmatterValue.textValue("zsh"))).to_be_nil()
expect(parseShellFrontmatter(FrontmatterValue.nilValue())).to_be_nil()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `73de0f01cdef1e0f65c89431e2ae4a45932fd299b3dcd9748514dad05978a673`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `73de0f01cdef1e0f65c89431e2ae4a45932fd299b3dcd9748514dad05978a673`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `73de0f01cdef1e0f65c89431e2ae4a45932fd299b3dcd9748514dad05978a673`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/utils/frontmatter_parser_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/frontmatter_parser_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/frontmatter_parser_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/frontmatter_parser_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/frontmatter_parser_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/frontmatter_parser_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'splits comma paths while respecting brace groups' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/frontmatter_parser_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'expands nested brace alternatives' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/frontmatter_parser_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flattens path lists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
