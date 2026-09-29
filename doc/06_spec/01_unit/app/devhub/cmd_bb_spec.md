# cmd_bb_spec

> Purpose: Prove that itf bb (dispatch, no network).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# cmd_bb_spec

Purpose: Prove that itf bb (dispatch, no network).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/devhub/cmd_bb_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that itf bb (dispatch, no network).
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### itf bb (dispatch, no network)

### top-level

#### no args prints help, rc 0

- no args prints help, rc 0
- Verify: no args prints help, rc 0
   - Expected: handle_bb([]) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("no args prints help, rc 0")
step("Verify: no args prints help, rc 0")
# @req: REQ-APP-DEVHUB-001
expect(handle_bb([])).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### --help prints help, rc 0

- --help prints help, rc 0
- Verify: --help prints help, rc 0
   - Expected: handle_bb(["--help"]) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("--help prints help, rc 0")
step("Verify: --help prints help, rc 0")
expect(handle_bb(["--help"])).to_equal(0)
```

</details>

#### unknown top-level command exits 1

- unknown top-level command exits 1
- Verify: unknown top-level command exits 1
   - Expected: handle_bb(["bogus"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("unknown top-level command exits 1")
step("Verify: unknown top-level command exits 1")
expect(handle_bb(["bogus"])).to_equal(1)
```

</details>

### repo

#### --help exits 0

- --help exits 0
- Verify: --help exits 0
   - Expected: handle_bb(["repo", "--help"]) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("--help exits 0")
step("Verify: --help exits 0")
expect(handle_bb(["repo", "--help"])).to_equal(0)
```

</details>

#### no subcommand prints help, rc 0

- no subcommand prints help, rc 0
- Verify: no subcommand prints help, rc 0
   - Expected: handle_bb(["repo"]) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("no subcommand prints help, rc 0")
step("Verify: no subcommand prints help, rc 0")
expect(handle_bb(["repo"])).to_equal(0)
```

</details>

#### list without --workspace/BB_WORKSPACE exits 1 with a usage error

- list without --workspace/BB_WORKSPACE exits 1 with a usage error
- Verify: list without --workspace/BB_WORKSPACE exits 1 with a usage error
   - Expected: handle_bb(["repo", "list"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("list without --workspace/BB_WORKSPACE exits 1 with a usage error")
step("Verify: list without --workspace/BB_WORKSPACE exits 1 with a usage error")
expect(handle_bb(["repo", "list"])).to_equal(1)
```

</details>

#### view without a slug exits 1

- view without a slug exits 1
- Verify: view without a slug exits 1
   - Expected: handle_bb(["repo", "view", "--workspace", "acme"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("view without a slug exits 1")
step("Verify: view without a slug exits 1")
expect(handle_bb(["repo", "view", "--workspace", "acme"])).to_equal(1)
```

</details>

#### view without --workspace exits 1

- view without --workspace exits 1
- Verify: view without --workspace exits 1
   - Expected: handle_bb(["repo", "view", "widgets"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("view without --workspace exits 1")
step("Verify: view without --workspace exits 1")
expect(handle_bb(["repo", "view", "widgets"])).to_equal(1)
```

</details>

#### unknown repo subcommand exits 1

- unknown repo subcommand exits 1
- Verify: unknown repo subcommand exits 1
   - Expected: handle_bb(["repo", "bogus"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("unknown repo subcommand exits 1")
step("Verify: unknown repo subcommand exits 1")
expect(handle_bb(["repo", "bogus"])).to_equal(1)
```

</details>

### pr

#### --help exits 0

- --help exits 0
- Verify: --help exits 0
   - Expected: handle_bb(["pr", "--help"]) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("--help exits 0")
step("Verify: --help exits 0")
expect(handle_bb(["pr", "--help"])).to_equal(0)
```

</details>

#### list without --workspace/--repo exits 1 with a usage error

- list without --workspace/--repo exits 1 with a usage error
- Verify: list without --workspace/--repo exits 1 with a usage error
   - Expected: handle_bb(["pr", "list"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("list without --workspace/--repo exits 1 with a usage error")
step("Verify: list without --workspace/--repo exits 1 with a usage error")
expect(handle_bb(["pr", "list"])).to_equal(1)
```

</details>

#### view without --workspace/--repo exits 1

- view without --workspace/--repo exits 1
- Verify: view without --workspace/--repo exits 1
   - Expected: handle_bb(["pr", "view", "5"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("view without --workspace/--repo exits 1")
step("Verify: view without --workspace/--repo exits 1")
expect(handle_bb(["pr", "view", "5"])).to_equal(1)
```

</details>

#### unknown pr subcommand exits 1

- unknown pr subcommand exits 1
- Verify: unknown pr subcommand exits 1
   - Expected: handle_bb(["pr", "bogus"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("unknown pr subcommand exits 1")
step("Verify: unknown pr subcommand exits 1")
expect(handle_bb(["pr", "bogus"])).to_equal(1)
```

</details>

### comment / approve / merge / status help (unaffected siblings)

#### comment --help exits 0

- comment --help exits 0
- Verify: comment --help exits 0
   - Expected: handle_bb(["comment", "--help"]) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("comment --help exits 0")
step("Verify: comment --help exits 0")
expect(handle_bb(["comment", "--help"])).to_equal(0)
```

</details>

### _bb_pr_row

#### formats id/title/state/author/branch/updated

- formats id/title/state/author/branch/updated
- Verify: formats id/title/state/author/branch/updated
   - Expected: row[0] equals `#7`
   - Expected: row[1] equals `Add foo`
   - Expected: row[3] equals `Ada`
   - Expected: row[4] equals `feat/foo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("formats id/title/state/author/branch/updated")
step("Verify: formats id/title/state/author/branch/updated")
val pr = BbPr(id: 7, title: "Add foo", state: "OPEN", source_branch: "feat/foo", dest_branch: "main", author: "Ada", web_url: "", merge_commit: "", updated_on: "2026-07-01T00:00:00.000000+00:00")
val row = _bb_pr_row(pr)
expect(row[0]).to_equal("#7")
expect(row[1]).to_equal("Add foo")
expect(row[3]).to_equal("Ada")
expect(row[4]).to_equal("feat/foo")
```

</details>

#### row has exactly 6 columns

- row has exactly 6 columns
- Verify: row has exactly 6 columns
   - Expected: _bb_pr_row(pr).len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("row has exactly 6 columns")
step("Verify: row has exactly 6 columns")
val pr = BbPr(id: 1, title: "T", state: "OPEN", source_branch: "s", dest_branch: "d", author: "a", web_url: "", merge_commit: "", updated_on: "")
expect(_bb_pr_row(pr).len()).to_equal(6)  # oracle: 6 — named expected value from the requirement
```

</details>

### _bb_repo_row

#### formats name/description/visibility/updated for a public repo

- formats name/description/visibility/updated for a public repo
- Verify: formats name/description/visibility/updated for a public repo
   - Expected: row[0] equals `Widgets`
   - Expected: row[1] equals `Widget factory`
   - Expected: row[2] equals `public`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("formats name/description/visibility/updated for a public repo")
step("Verify: formats name/description/visibility/updated for a public repo")
val r = BbRepo(slug: "widgets", name: "Widgets", full_name: "acme/widgets", description: "Widget factory", is_private: false, updated_on: "2026-07-01T00:00:00.000000+00:00", main_branch: "main", web_url: "")
val row = _bb_repo_row(r)
expect(row[0]).to_equal("Widgets")
expect(row[1]).to_equal("Widget factory")
expect(row[2]).to_equal("public")
```

</details>

#### marks a private repo as private

- marks a private repo as private
- Verify: marks a private repo as private
   - Expected: row[2] equals `private`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("marks a private repo as private")
step("Verify: marks a private repo as private")
val r = BbRepo(slug: "secret", name: "Secret", full_name: "acme/secret", description: "", is_private: true, updated_on: "", main_branch: "", web_url: "")
val row = _bb_repo_row(r)
expect(row[2]).to_equal("private")
```

</details>

#### row has exactly 4 columns

- row has exactly 4 columns
- Verify: row has exactly 4 columns
   - Expected: _bb_repo_row(r).len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("row has exactly 4 columns")
step("Verify: row has exactly 4 columns")
val r = BbRepo(slug: "s", name: "S", full_name: "a/s", description: "", is_private: false, updated_on: "", main_branch: "", web_url: "")
expect(_bb_repo_row(r).len()).to_equal(4)  # oracle: 4 — named expected value from the requirement
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
- `REQ-APP-DEVHUB-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c26c55908e027fba2e510f6014f3961830e2c06d312fdf4e0b0e55bb7d5f96bf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c26c55908e027fba2e510f6014f3961830e2c06d312fdf4e0b0e55bb7d5f96bf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c26c55908e027fba2e510f6014f3961830e2c06d312fdf4e0b0e55bb7d5f96bf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/app/devhub/cmd_bb_spec.spl
mirror: doc/06_spec/01_unit/app/devhub/cmd_bb_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/devhub/cmd_bb_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/devhub/cmd_bb_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/devhub/cmd_bb_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 13 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/devhub/cmd_bb_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'no args prints help, rc 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/devhub/cmd_bb_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '--help prints help, rc 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/devhub/cmd_bb_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'unknown top-level command exits 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
