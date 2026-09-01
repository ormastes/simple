# tag_parsing_spec

> Purpose: extracts # comment lines

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# tag_parsing_spec

Purpose: extracts # comment lines

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/unit/test_runner/tag_parsing_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: extracts # comment lines
Audience: compiler and tooling engineers who maintain this spec

## Scenarios

### extract_directive_lines

#### extracts # comment lines

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- extracts # comment lines
- Verify: extracts # comment lines
   - Expected: lines.length equals `2`
   - Expected: lines[0] equals `# @tag:system`
   - Expected: lines[1] equals `# @mode:native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts # comment lines")
step("Verify: extracts # comment lines")
# @req: REQ-TEST_RUNNER-TagPars-001
val content = "# @tag:system\nuse std.spec\n# @mode:native"
val lines = extract_directive_lines(content)
expect(lines.length).to_equal(2)  # oracle: value fixed by the spec contract
expect(lines[0]).to_equal("# @tag:system")
expect(lines[1]).to_equal("# @mode:native")
```

</details>

#### extracts directives from inside docstrings

- extracts directives from inside docstrings
- Verify: extracts directives from inside docstrings
   - Expected: lines.length equals `3`
   - Expected: lines[0] equals `# @tag:api`
   - Expected: lines[1] equals `@mode:interpreter`
   - Expected: lines[2] equals `# @tag:system`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts directives from inside docstrings")
step("Verify: extracts directives from inside docstrings")
# @req: REQ-TEST_RUNNER-TagPars-001
val content = "\"\"\"\n# @tag:api\n@mode:interpreter\nSome text\n\"\"\"\n# @tag:system"
val lines = extract_directive_lines(content)
expect(lines.length).to_equal(3)  # oracle: value fixed by the spec contract
expect(lines[0]).to_equal("# @tag:api")
expect(lines[1]).to_equal("@mode:interpreter")
expect(lines[2]).to_equal("# @tag:system")
```

</details>

#### ignores non-directive lines in docstrings

- ignores non-directive lines in docstrings
- Verify: ignores non-directive lines in docstrings
   - Expected: lines.length equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignores non-directive lines in docstrings")
step("Verify: ignores non-directive lines in docstrings")
# @req: REQ-TEST_RUNNER-TagPars-001
val content = "\"\"\"\nSome doc text\n**Category:** Tooling\n\"\"\""
val lines = extract_directive_lines(content)
expect(lines.length).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### handles empty content

- handles empty content
- Verify: handles empty content
   - Expected: lines.length equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty content")
step("Verify: handles empty content")
# @req: REQ-TEST_RUNNER-TagPars-001
val lines = extract_directive_lines("")
expect(lines.length).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

### extract_tags

#### parses single tag from comment

- parses single tag from comment
- Verify: parses single tag from comment
   - Expected: extract_tags("# @tag:system") equals `system`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses single tag from comment")
step("Verify: parses single tag from comment")
# @req: REQ-TEST_RUNNER-TagPars-001
expect(extract_tags("# @tag:system")).to_equal("system")
```

</details>

#### parses comma-separated tags

- parses comma-separated tags
- Verify: parses comma-separated tags
   - Expected: extract_tags("# @tag:slow,system") equals `slow,system`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses comma-separated tags")
step("Verify: parses comma-separated tags")
# @req: REQ-TEST_RUNNER-TagPars-001
expect(extract_tags("# @tag:slow,system")).to_equal("slow,system")
```

</details>

#### parses tag with spaces after comma

- parses tag with spaces after comma
- Verify: parses tag with spaces after comma
   - Expected: extract_tags("# @tag:slow, system") equals `slow,system`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses tag with spaces after comma")
step("Verify: parses tag with spaces after comma")
# @req: REQ-TEST_RUNNER-TagPars-001
expect(extract_tags("# @tag:slow, system")).to_equal("slow,system")
```

</details>

#### parses tag from inside docstring

- parses tag from inside docstring
- Verify: parses tag from inside docstring
   - Expected: extract_tags(content) equals `api`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses tag from inside docstring")
step("Verify: parses tag from inside docstring")
# @req: REQ-TEST_RUNNER-TagPars-001
val content = "\"\"\"\n@tag:api\n\"\"\""
expect(extract_tags(content)).to_equal("api")
```

</details>

#### parses tags from both comment and docstring

- parses tags from both comment and docstring
- Verify: parses tags from both comment and docstring
   - Expected: extract_tags(content) equals `system,internal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses tags from both comment and docstring")
step("Verify: parses tags from both comment and docstring")
# @req: REQ-TEST_RUNNER-TagPars-001
val content = "# @tag:system\n\"\"\"\n@tag:internal\n\"\"\""
expect(extract_tags(content)).to_equal("system,internal")
```

</details>

#### strips quotes from tag values

- strips quotes from tag values
- Verify: strips quotes from tag values
   - Expected: extract_tags("# @tag:\"only-compiled\"") equals `only-compiled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strips quotes from tag values")
step("Verify: strips quotes from tag values")
# @req: REQ-TEST_RUNNER-TagPars-001
expect(extract_tags("# @tag:\"only-compiled\"")).to_equal("only-compiled")
```

</details>

#### strips brackets and quotes

- strips brackets and quotes
- Verify: strips brackets and quotes
   - Expected: extract_tags("# @tag:[\"only-compiled\"]") equals `only-compiled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strips brackets and quotes")
step("Verify: strips brackets and quotes")
# @req: REQ-TEST_RUNNER-TagPars-001
expect(extract_tags("# @tag:[\"only-compiled\"]")).to_equal("only-compiled")
```

</details>

#### excludes skip and pending

- excludes skip and pending
- Verify: excludes skip and pending
   - Expected: extract_tags("# @tag:skip") equals ``
   - Expected: extract_tags("# @tag:pending") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("excludes skip and pending")
step("Verify: excludes skip and pending")
# @req: REQ-TEST_RUNNER-TagPars-001
expect(extract_tags("# @tag:skip")).to_equal("")
expect(extract_tags("# @tag:pending")).to_equal("")
```

</details>

#### deduplicates tags

- deduplicates tags
- Verify: deduplicates tags
   - Expected: extract_tags(content) equals `system`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("deduplicates tags")
step("Verify: deduplicates tags")
# @req: REQ-TEST_RUNNER-TagPars-001
val content = "# @tag:system\n# @tag:system"
expect(extract_tags(content)).to_equal("system")
```

</details>

### extract_mode_tags

#### parses mode from comment

- parses mode from comment
- Verify: parses mode from comment
   - Expected: extract_mode_tags("# @mode:interpreter") equals `interpreter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses mode from comment")
step("Verify: parses mode from comment")
# @req: REQ-TEST_RUNNER-TagPars-001
expect(extract_mode_tags("# @mode:interpreter")).to_equal("interpreter")
```

</details>

#### parses mode from docstring

- parses mode from docstring
- Verify: parses mode from docstring
   - Expected: extract_mode_tags(content) equals `native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses mode from docstring")
step("Verify: parses mode from docstring")
# @req: REQ-TEST_RUNNER-TagPars-001
val content = "\"\"\"\n@mode:native\n\"\"\""
expect(extract_mode_tags(content)).to_equal("native")
```

</details>

#### parses skip_mode with ! prefix

- parses skip_mode with ! prefix
- Verify: parses skip_mode with ! prefix
   - Expected: extract_mode_tags("# @skip_mode:native") equals `!native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses skip_mode with ! prefix")
step("Verify: parses skip_mode with ! prefix")
# @req: REQ-TEST_RUNNER-TagPars-001
expect(extract_mode_tags("# @skip_mode:native")).to_equal("!native")
```

</details>

#### parses comma-separated modes

- parses comma-separated modes
- Verify: parses comma-separated modes
   - Expected: extract_mode_tags("# @mode:interpreter,native") equals `interpreter,native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses comma-separated modes")
step("Verify: parses comma-separated modes")
# @req: REQ-TEST_RUNNER-TagPars-001
expect(extract_mode_tags("# @mode:interpreter,native")).to_equal("interpreter,native")
```

</details>

#### handles mixed comment and docstring

- handles mixed comment and docstring
- Verify: handles mixed comment and docstring
   - Expected: extract_mode_tags(content) equals `interpreter,!native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles mixed comment and docstring")
step("Verify: handles mixed comment and docstring")
# @req: REQ-TEST_RUNNER-TagPars-001
val content = "# @mode:interpreter\n\"\"\"\n@skip_mode:native\n\"\"\""
expect(extract_mode_tags(content)).to_equal("interpreter,!native")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-TEST_RUNNER-TagPars-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `14fdf21849718234c64126da387ff3c665df4679eec863a7f424d99cccf200f6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `14fdf21849718234c64126da387ff3c665df4679eec863a7f424d99cccf200f6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `14fdf21849718234c64126da387ff3c665df4679eec863a7f424d99cccf200f6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **81/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/unit/test_runner/tag_parsing_spec.spl
mirror: doc/06_spec/unit/test_runner/tag_parsing_spec.md (current)
findings: 4 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=81; blocker cap makes effective=49
doc/06_spec/unit/test_runner/tag_parsing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/test_runner/tag_parsing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/test_runner/tag_parsing_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/unit/test_runner/tag_parsing_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
<!-- sspec-maintain:scorecard:end -->
