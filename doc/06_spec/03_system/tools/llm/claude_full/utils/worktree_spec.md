# Claude Full Worktree Slice

> Focused Simple coverage for pure worktree naming and PR parsing helpers from

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Worktree Slice

Focused Simple coverage for pure worktree naming and PR parsing helpers from

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/worktree_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused Simple coverage for pure worktree naming and PR parsing helpers from
utils/worktree.ts.

## Scenarios

### Claude full worktree parity

#### should model worktree slug validation

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should model worktree slug validation
- Check slug validation
   - Expected: validateWorktreeSlugRoute("user/feature-1") equals `valid`
   - Expected: validateWorktreeSlugRoute("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa") equals `valid`
   - Expected: validateWorktreeSlugRoute("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa") equals `slug too long`
   - Expected: validateWorktreeSlugRoute("a/./b") equals `invalid path segment`
   - Expected: validateWorktreeSlugRoute("a/../b") equals `invalid path segment`
   - Expected: validateWorktreeSlugRoute("/a") equals `invalid empty segment`
   - Expected: validateWorktreeSlugRoute("a/") equals `invalid empty segment`
   - Expected: validateWorktreeSlugRoute("a//b") equals `invalid empty segment`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model worktree slug validation")
step("Check slug validation")
expect(validateWorktreeSlugRoute("user/feature-1")).to_equal("valid")
expect(validateWorktreeSlugRoute("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")).to_equal("valid")
expect(validateWorktreeSlugRoute("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")).to_equal("slug too long")
expect(validateWorktreeSlugRoute("a/./b")).to_equal("invalid path segment")
expect(validateWorktreeSlugRoute("a/../b")).to_equal("invalid path segment")
expect(validateWorktreeSlugRoute("/a")).to_equal("invalid empty segment")
expect(validateWorktreeSlugRoute("a/")).to_equal("invalid empty segment")
expect(validateWorktreeSlugRoute("a//b")).to_equal("invalid empty segment")
```

</details>

#### should model branch and tmux names

- should model branch and tmux names
- Check generated names
   - Expected: flattenSlugRoute("a/b.c") equals `a+b.c`
   - Expected: worktreeBranchNameRoute("a/b.c") equals `worktree-a+b.c`
   - Expected: generateTmuxSessionNameRoute("/tmp/my.repo", "branch/a.b") equals `my_repo_branch_a_b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model branch and tmux names")
step("Check generated names")
expect(flattenSlugRoute("a/b.c")).to_equal("a+b.c")
expect(worktreeBranchNameRoute("a/b.c")).to_equal("worktree-a+b.c")
expect(generateTmuxSessionNameRoute("/tmp/my.repo", "branch/a.b")).to_equal("my_repo_branch_a_b")
```

</details>

#### should model PR reference parsing

- should model PR reference parsing
- Check PR references
   - Expected: parsePRReferenceRoute("#123") equals `123`
   - Expected: parsePRReferenceRoute("https://host/owner/repo/pull/123?x=1#y") equals `123`
   - Expected: parsePRReferenceRoute("pull/123") equals `null`
   - Expected: parsePRReferenceRoute("https://host/owner/repo/-/merge_requests/123") equals `null`
   - Expected: worktreeSourceLinesModeled() equals `1519`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model PR reference parsing")
step("Check PR references")
expect(parsePRReferenceRoute("#123")).to_equal("123")
expect(parsePRReferenceRoute("https://host/owner/repo/pull/123?x=1#y")).to_equal("123")
expect(parsePRReferenceRoute("pull/123")).to_equal("null")
expect(parsePRReferenceRoute("https://host/owner/repo/-/merge_requests/123")).to_equal("null")
expect(worktreeSourceLinesModeled()).to_equal(1519)
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

- Canonical SPipe generation for source `0886d6b2e5f210c41b5705ce2efe1a3e03de6561d9fa546c6f43ef4c06786b01`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0886d6b2e5f210c41b5705ce2efe1a3e03de6561d9fa546c6f43ef4c06786b01`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0886d6b2e5f210c41b5705ce2efe1a3e03de6561d9fa546c6f43ef4c06786b01`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/utils/worktree_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/worktree_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/worktree_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/worktree_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/worktree_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/worktree_spec.spl:19:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model worktree slug validation' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/worktree_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model worktree slug validation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/worktree_spec.spl:32:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model branch and tmux names' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/worktree_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model branch and tmux names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/worktree_spec.spl:40:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model PR reference parsing' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/worktree_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model PR reference parsing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
