# Forbidden Verbs Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Forbidden Verbs Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/sj/forbidden_verbs_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

#
#
#
#

## Scenarios

### Forbidden Verbs - Interactive Rebase

#### forbids git rebase -i

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- forbids git rebase -i
   - Expected: result.allowed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("forbids git rebase -i")
val result = check_forbidden(["git", "rebase", "-i"])
expect(result.allowed).to_equal(false)
expect(result.message).to_contain("FORBIDDEN")
expect(result.message).to_contain("rebase -i")
```

</details>

#### allows git rebase without -i

- allows git rebase without -i
   - Expected: result.allowed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows git rebase without -i")
val result = check_forbidden(["git", "rebase", "main"])
expect(result.allowed).to_equal(true)
```

</details>

### Forbidden Verbs - Force Push

#### forbids git push --force

- forbids git push --force
   - Expected: result.allowed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("forbids git push --force")
val result = check_forbidden(["git", "push", "--force"])
expect(result.allowed).to_equal(false)
expect(result.message).to_contain("force-push")
```

</details>

#### forbids git push -f

- forbids git push -f
   - Expected: result.allowed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("forbids git push -f")
val result = check_forbidden(["git", "push", "-f"])
expect(result.allowed).to_equal(false)
```

</details>

#### allows git push with --bookmark

- allows git push with --bookmark
   - Expected: result.allowed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows git push with --bookmark")
val result = check_forbidden(["git", "push", "--bookmark", "main"])
expect(result.allowed).to_equal(true)
```

</details>

### Forbidden Verbs - Bare Push

#### forbids bare git push

- forbids bare git push
   - Expected: result.allowed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("forbids bare git push")
val result = check_forbidden(["git", "push"])
expect(result.allowed).to_equal(false)
expect(result.message).to_contain("ambiguous")
```

</details>

#### allows git push with --via-worktree

- allows git push with --via-worktree
   - Expected: result.allowed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows git push with --via-worktree")
val result = check_forbidden(["git", "push", "--via-worktree"])
expect(result.allowed).to_equal(true)
```

</details>

### Forbidden Verbs - Bare Checkout

#### forbids bare git checkout

- forbids bare git checkout
   - Expected: result.allowed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("forbids bare git checkout")
val result = check_forbidden(["git", "checkout"])
expect(result.allowed).to_equal(false)
expect(result.message).to_contain("not meaningful")
```

</details>

#### allows git checkout with rev

- allows git checkout with rev
   - Expected: result.allowed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows git checkout with rev")
val result = check_forbidden(["git", "checkout", "main"])
expect(result.allowed).to_equal(true)
```

</details>

### Forbidden Verbs - Filter-Branch

#### forbids git filter-branch

- forbids git filter-branch
   - Expected: result.allowed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("forbids git filter-branch")
val result = check_forbidden(["git", "filter-branch"])
expect(result.allowed).to_equal(false)
expect(result.message).to_contain("filter-branch")
```

</details>

### Forbidden Verbs - Stash

#### forbids git stash

- forbids git stash
   - Expected: result.allowed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("forbids git stash")
val result = check_forbidden(["git", "stash"])
expect(result.allowed).to_equal(false)
expect(result.message).to_contain("jj new")
```

</details>

### Forbidden Verbs - Passthrough

#### allows non-git commands

- allows non-git commands
   - Expected: result.allowed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows non-git commands")
val result = check_forbidden(["describe", "-m", "test"])
expect(result.allowed).to_equal(true)
```

</details>

#### allows empty argv

- allows empty argv
   - Expected: result.allowed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows empty argv")
val result = check_forbidden([])
expect(result.allowed).to_equal(true)
```

</details>

#### allows single git with no verb

- allows single git with no verb
   - Expected: result.allowed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows single git with no verb")
val result = check_forbidden(["git"])
expect(result.allowed).to_equal(true)
```

</details>

### Forbidden Verbs - PolicyResult contract

#### an allowed result carries exit_code 0 and an empty message

- an allowed result carries exit_code 0 and an empty message
   - Expected: result.allowed is true
   - Expected: result.exit_code equals `0i64`
   - Expected: result.message equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an allowed result carries exit_code 0 and an empty message")
val result = check_forbidden(["git", "rebase", "main"])
expect(result.allowed).to_equal(true)
expect(result.exit_code).to_equal(0i64)
expect(result.message).to_equal("")
```

</details>

#### a forbidden result carries exit_code 1

- a forbidden result carries exit_code 1
   - Expected: result.allowed is false
   - Expected: result.exit_code equals `1i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a forbidden result carries exit_code 1")
val result = check_forbidden(["git", "stash"])
expect(result.allowed).to_equal(false)
expect(result.exit_code).to_equal(1i64)
```

</details>

#### every forbidden message is prefixed ERROR[FORBIDDEN]

- every forbidden message is prefixed ERROR[FORBIDDEN]


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("every forbidden message is prefixed ERROR[FORBIDDEN]")
expect(check_forbidden(["git", "rebase", "-i"]).message).to_start_with("ERROR[FORBIDDEN]:")
expect(check_forbidden(["git", "push", "--force"]).message).to_start_with("ERROR[FORBIDDEN]:")
expect(check_forbidden(["git", "push"]).message).to_start_with("ERROR[FORBIDDEN]:")
expect(check_forbidden(["git", "checkout"]).message).to_start_with("ERROR[FORBIDDEN]:")
expect(check_forbidden(["git", "filter-branch"]).message).to_start_with("ERROR[FORBIDDEN]:")
expect(check_forbidden(["git", "stash"]).message).to_start_with("ERROR[FORBIDDEN]:")
```

</details>

### Forbidden Verbs - argument-scan edges

#### rebase -i is caught wherever -i appears in argv

- rebase -i is caught wherever -i appears in argv
   - Expected: result.allowed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rebase -i is caught wherever -i appears in argv")
val result = check_forbidden(["git", "rebase", "--onto", "main", "-i"])
expect(result.allowed).to_equal(false)
expect(result.message).to_contain("rebase -i")
```

</details>

#### force-push is caught behind other flags

- force-push is caught behind other flags
   - Expected: result.allowed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("force-push is caught behind other flags")
val result = check_forbidden(["git", "push", "origin", "main", "--force"])
expect(result.allowed).to_equal(false)
expect(result.message).to_contain("force-push")
```

</details>

#### a non-bare push with a rev is allowed

- a non-bare push with a rev is allowed
   - Expected: result.allowed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a non-bare push with a rev is allowed")
val result = check_forbidden(["git", "push", "origin", "main"])
expect(result.allowed).to_equal(true)
```

</details>

#### stash is forbidden regardless of trailing arguments

- stash is forbidden regardless of trailing arguments
   - Expected: result.allowed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stash is forbidden regardless of trailing arguments")
val result = check_forbidden(["git", "stash", "pop"])
expect(result.allowed).to_equal(false)
expect(result.message).to_contain("jj new")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8e7311ebbbb1dafd709354603237d08d6d3f79acf81fc9147505c06f4280e40e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8e7311ebbbb1dafd709354603237d08d6d3f79acf81fc9147505c06f4280e40e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8e7311ebbbb1dafd709354603237d08d6d3f79acf81fc9147505c06f4280e40e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/sj/forbidden_verbs_spec.spl
mirror: doc/06_spec/unit/app/sj/forbidden_verbs_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/sj/forbidden_verbs_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/sj/forbidden_verbs_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/sj/forbidden_verbs_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'forbids git rebase -i' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/sj/forbidden_verbs_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows git rebase without -i' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/sj/forbidden_verbs_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'forbids git push --force' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
