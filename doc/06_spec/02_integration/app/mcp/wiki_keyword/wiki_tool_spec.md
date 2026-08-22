# MCP Wiki Keyword Tool Specification

> Verifies the wiki tool behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Wiki Keyword Tool Specification

Verifies the wiki tool behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Red (no impl yet) |
| Source | `test/02_integration/app/mcp/wiki_keyword/wiki_tool_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the wiki tool behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### MCP wiki_keyword tool

### wiki_lookup

#### AC-6: returns Content tagged with ContentAuthority

- Verify: AC-6: returns Content tagged with ContentAuthority


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-WIKI_KEYWORD_WIKI_TOOL-001
step("Verify: AC-6: returns Content tagged with ContentAuthority")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val result = wiki_lookup("simple language")
expect result.ok to_equal true
val authority = result.value.authority
expect authority.level to_equal AuthorityLevel.Internal
expect authority.source_trust to_equal TrustSource.RegistryTrusted
```

</details>

#### AC-6: release_gate returns Scrub/Block for lower-clearance reader

- Verify: AC-6: release_gate returns Scrub/Block for lower-clearance reader


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-WIKI_KEYWORD_WIKI_TOOL-001
step("Verify: AC-6: release_gate returns Scrub/Block for lower-clearance reader")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val result = wiki_lookup("simple language")
val decision = release_gate(result.value.authority, AuthorityLevel.Public)
val held = (decision.kind == "Scrub") or (decision.kind == "Block")
expect held to_equal true
```

</details>

### registration via dispatch_wrap

#### AC-6: register_wiki_tool adds tool entry to DispatchRegistry

- Verify: AC-6: register_wiki_tool adds tool entry to DispatchRegistry


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-WIKI_KEYWORD_WIKI_TOOL-001
step("Verify: AC-6: register_wiki_tool adds tool entry to DispatchRegistry")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val reg = DispatchRegistry.new()
register_wiki_tool(reg)
val found = reg.find("wiki.lookup")
expect found.present to_equal true
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3dc3aaf9ed7b52afd7be807c687322d46212dcb1a01246ac111898d2ba90beb9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3dc3aaf9ed7b52afd7be807c687322d46212dcb1a01246ac111898d2ba90beb9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3dc3aaf9ed7b52afd7be807c687322d46212dcb1a01246ac111898d2ba90beb9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/app/mcp/wiki_keyword/wiki_tool_spec.spl
mirror: doc/06_spec/02_integration/app/mcp/wiki_keyword/wiki_tool_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/mcp/wiki_keyword/wiki_tool_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/app/mcp/wiki_keyword/wiki_tool_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/mcp/wiki_keyword/wiki_tool_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
