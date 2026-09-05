# Claude Full Bash Parser Slice

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Bash Parser Slice

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/bash/bashParser_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Claude full bash parser parity

#### should model lexer parser safety and command routing

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should model lexer parser safety and command routing
- Check lexer and safety routes
   - Expected: node.kind equals `program`
   - Expected: token.textValue equals `echo`
   - Expected: nextTokenModeRoute("[[", true) equals `cmd mode test operator`
   - Expected: nextTokenModeRoute("[[", false) equals `arg mode word token`
   - Expected: nextTokenModeRoute("<<EOF", true) equals `heredoc redirect token`
   - Expected: scannerWhitespaceRoute("crlf") equals `newline token from crlf`
   - Expected: scannerWhitespaceRoute("lineContinuation") equals `skip escaped newline`
   - Expected: checkBudgetRoute(0) equals `parse budget exhausted`
   - Expected: parseStatementsRoute(";;") equals `stop statements at closer`
   - Expected: parseStatementsRoute("#") equals `emit comment`
   - Expected: parsePipelineRoute("|&", true) equals `pipe stderr stdout with rhs redirect hoist`
   - Expected: parsePipelineRoute("|", true) equals `pipe with rhs redirect hoist`
   - Expected: parseSimpleCommandRoute(true, true, false) equals `simple command assignment redirect`
   - Expected: parseSimpleCommandRoute(false, false, true) equals `function definition precheck`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model lexer parser safety and command routing")
step("Check lexer and safety routes")
val node = TsNode.new("program", 0, 4)
expect(node.kind).to_equal("program")
val token = Token.new("word", "echo")
expect(token.textValue).to_equal("echo")
expect(nextTokenModeRoute("[[", true)).to_equal("cmd mode test operator")
expect(nextTokenModeRoute("[[", false)).to_equal("arg mode word token")
expect(nextTokenModeRoute("<<EOF", true)).to_equal("heredoc redirect token")
expect(scannerWhitespaceRoute("crlf")).to_equal("newline token from crlf")
expect(scannerWhitespaceRoute("lineContinuation")).to_equal("skip escaped newline")
expect(checkBudgetRoute(0)).to_equal("parse budget exhausted")
expect(parseStatementsRoute(";;")).to_equal("stop statements at closer")
expect(parseStatementsRoute("#")).to_equal("emit comment")
expect(parsePipelineRoute("|&", true)).to_equal("pipe stderr stdout with rhs redirect hoist")
expect(parsePipelineRoute("|", true)).to_equal("pipe with rhs redirect hoist")
expect(parseSimpleCommandRoute(true, true, false)).to_equal("simple command assignment redirect")
expect(parseSimpleCommandRoute(false, false, true)).to_equal("function definition precheck")
```

</details>

#### should model assignments redirects heredocs and words

- should model assignments redirects heredocs and words
- Check assignment redirect heredoc and word routes
   - Expected: assignmentRoute(false, "=", false) equals `not assignment`
   - Expected: assignmentRoute(true, "+=", true) equals `append array assignment`
   - Expected: assignmentRoute(true, "=", true) equals `array assignment`
   - Expected: redirectRoute(false, ">", false) equals `redirect missing target`
   - Expected: redirectRoute(true, ">", true) equals `fd redirect greedy target`
   - Expected: redirectRoute(false, "<>", true) equals `read write redirect`
   - Expected: redirectRoute(false, "<<-", true) equals `heredoc redirect pending`
   - Expected: heredocRoute("<<-", true) equals `quoted tab stripping heredoc start`
   - Expected: heredocRoute("<<", false) equals `interpolated heredoc start`
   - Expected: parseWordRoute(true, true, false, false) equals `quoted word with expansion`
   - Expected: parseWordRoute(false, false, true, false) equals `word with backtick`
   - Expected: parseWordRoute(false, false, false, true) equals `word with brace boundary`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model assignments redirects heredocs and words")
step("Check assignment redirect heredoc and word routes")
expect(assignmentRoute(false, "=", false)).to_equal("not assignment")
expect(assignmentRoute(true, "+=", true)).to_equal("append array assignment")
expect(assignmentRoute(true, "=", true)).to_equal("array assignment")
expect(redirectRoute(false, ">", false)).to_equal("redirect missing target")
expect(redirectRoute(true, ">", true)).to_equal("fd redirect greedy target")
expect(redirectRoute(false, "<>", true)).to_equal("read write redirect")
expect(redirectRoute(false, "<<-", true)).to_equal("heredoc redirect pending")
expect(heredocRoute("<<-", true)).to_equal("quoted tab stripping heredoc start")
expect(heredocRoute("<<", false)).to_equal("interpolated heredoc start")
expect(parseWordRoute(true, true, false, false)).to_equal("quoted word with expansion")
expect(parseWordRoute(false, false, true, false)).to_equal("word with backtick")
expect(parseWordRoute(false, false, false, true)).to_equal("word with brace boundary")
```

</details>

#### should model expansions controls tests arithmetic and source floor

- should model expansions controls tests arithmetic and source floor
- Check expansion control and expression routes
   - Expected: expansionRoute("arith", false) equals `parse arithmetic expansion`
   - Expected: expansionRoute("brace", false) equals `parse parameter expansion`
   - Expected: expansionRoute("regex", true) equals `parse segmented regex expansion`
   - Expected: expansionRoute("array", false) equals `parse array expansion`
   - Expected: controlRoute("if") equals `parse if command`
   - Expected: controlRoute("case") equals `parse case command`
   - Expected: controlRoute("function") equals `parse function command`
   - Expected: testExprRoute("regex") equals `test regex rhs`
   - Expected: testExprRoute("extglob") equals `test extglob rhs`
   - Expected: arithmeticRoute("var", false, "") equals `arithmetic variable mode`
   - Expected: arithmeticRoute("expr", true, "") equals `arithmetic right associative assignment`
   - Expected: arithmeticRoute("expr", false, "))") equals `arithmetic stop boundary`
   - Expected: bashParserSourceLinesModeled() equals `4436`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model expansions controls tests arithmetic and source floor")
step("Check expansion control and expression routes")
expect(expansionRoute("arith", false)).to_equal("parse arithmetic expansion")
expect(expansionRoute("brace", false)).to_equal("parse parameter expansion")
expect(expansionRoute("regex", true)).to_equal("parse segmented regex expansion")
expect(expansionRoute("array", false)).to_equal("parse array expansion")
expect(controlRoute("if")).to_equal("parse if command")
expect(controlRoute("case")).to_equal("parse case command")
expect(controlRoute("function")).to_equal("parse function command")
expect(testExprRoute("regex")).to_equal("test regex rhs")
expect(testExprRoute("extglob")).to_equal("test extglob rhs")
expect(arithmeticRoute("var", false, "")).to_equal("arithmetic variable mode")
expect(arithmeticRoute("expr", true, "")).to_equal("arithmetic right associative assignment")
expect(arithmeticRoute("expr", false, "))")).to_equal("arithmetic stop boundary")
expect(bashParserSourceLinesModeled()).to_equal(4436)
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

- Canonical SPipe generation for source `99314f3136c785788a6eab5b54cf10e904a50e1adb2e4f5dfe289245c03c09ea`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `99314f3136c785788a6eab5b54cf10e904a50e1adb2e4f5dfe289245c03c09ea`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `99314f3136c785788a6eab5b54cf10e904a50e1adb2e4f5dfe289245c03c09ea`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/utils/bash/bashParser_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/bash/bashParser_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/bash/bashParser_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/bash/bashParser_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/bash/bashParser_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/bash/bashParser_spec.spl:16:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model lexer parser safety and command routing' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/bash/bashParser_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model lexer parser safety and command routing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/bash/bashParser_spec.spl:37:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model assignments redirects heredocs and words' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/bash/bashParser_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model assignments redirects heredocs and words' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/bash/bashParser_spec.spl:54:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model expansions controls tests arithmetic and source floor' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/bash/bashParser_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model expansions controls tests arithmetic and source floor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
