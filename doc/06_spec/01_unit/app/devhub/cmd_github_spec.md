# cmd_github_spec

> Purpose: Prove that itf github (fake-binary fixture).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# cmd_github_spec

Purpose: Prove that itf github (fake-binary fixture).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/devhub/cmd_github_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that itf github (fake-binary fixture).
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### itf github (fake-binary fixture)

#### issue list — success path

#### exits 0 and forwards the default --json fields to gh

- exits 0 and forwards the default --json fields to gh
- Verify: exits 0 and forwards the default --json fields to gh
   - Expected: code equals `0`
   - Expected: log contains `issue list --json number,title,state,author,updatedAt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("exits 0 and forwards the default --json fields to gh")
step("Verify: exits 0 and forwards the default --json fields to gh")
# @req: REQ-APP-DEVHUB-001
val dir = install_fake_gh(FAKE_GH_LIST_OK)
val (code, log) = run_github_with_fake_gh(dir, ["issue", "list"])
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(log.contains("issue list --json number,title,state,author,updatedAt")).to_equal(true)
```

</details>

#### forwards extra gh-native flags (e.g. --state, --limit) verbatim

- forwards extra gh-native flags (e.g. --state, --limit) verbatim
- Verify: forwards extra gh-native flags (e.g. --state, --limit) verbatim
   - Expected: code equals `0`
   - Expected: log contains `--state open --limit 5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("forwards extra gh-native flags (e.g. --state, --limit) verbatim")
step("Verify: forwards extra gh-native flags (e.g. --state, --limit) verbatim")
val dir = install_fake_gh(FAKE_GH_LIST_OK)
val (code, log) = run_github_with_fake_gh(dir, ["issue", "list", "--state", "open", "--limit", "5"])
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(log.contains("--state open --limit 5")).to_equal(true)
```

</details>

#### pr list — empty result

#### exits 0 on an empty array (no issues/PRs is not an error)

- exits 0 on an empty array (no issues/PRs is not an error)
- Verify: exits 0 on an empty array (no issues/PRs is not an error)
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("exits 0 on an empty array (no issues/PRs is not an error)")
step("Verify: exits 0 on an empty array (no issues/PRs is not an error)")
val dir = install_fake_gh(FAKE_GH_LIST_OK)
val (code, _log) = run_github_with_fake_gh(dir, ["pr", "list"])
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### gh missing

#### exits 1 with an actionable 'not found' error (never a bare crash)

- exits 1 with an actionable 'not found' error (never a bare crash)
- Verify: exits 1 with an actionable 'not found' error (never a bare crash)
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("exits 1 with an actionable 'not found' error (never a bare crash)")
step("Verify: exits 1 with an actionable 'not found' error (never a bare crash)")
val dir = install_fake_gh(FAKE_GH_NOT_FOUND)
val (code, _log) = run_github_with_fake_gh(dir, ["issue", "list"])
expect(code).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### gh unauthenticated

#### exits 1 and does not fall through to a bare exit code

- exits 1 and does not fall through to a bare exit code
- Verify: exits 1 and does not fall through to a bare exit code
   - Expected: code equals `1`
   - Expected: log contains `issue list`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("exits 1 and does not fall through to a bare exit code")
step("Verify: exits 1 and does not fall through to a bare exit code")
val dir = install_fake_gh(FAKE_GH_UNAUTHED)
val (code, log) = run_github_with_fake_gh(dir, ["issue", "list"])
expect(code).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(log.contains("issue list")).to_equal(true)
```

</details>

#### issue edit — passthrough

#### exits 0 and forwards the number and flags verbatim to gh

- exits 0 and forwards the number and flags verbatim to gh
- Verify: exits 0 and forwards the number and flags verbatim to gh
   - Expected: code equals `0`
   - Expected: log contains `issue edit 123 --add-label bug`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("exits 0 and forwards the number and flags verbatim to gh")
step("Verify: exits 0 and forwards the number and flags verbatim to gh")
val dir = install_fake_gh(FAKE_GH_PASSTHROUGH_OK)
val (code, log) = run_github_with_fake_gh(dir, ["issue", "edit", "123", "--add-label", "bug"])
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(log.contains("issue edit 123 --add-label bug")).to_equal(true)
```

</details>

#### repo clone — passthrough

#### exits 0 and forwards the repo name and directory verbatim to gh

- exits 0 and forwards the repo name and directory verbatim to gh
- Verify: exits 0 and forwards the repo name and directory verbatim to gh
   - Expected: code equals `0`
   - Expected: log contains `repo clone owner/name dest`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("exits 0 and forwards the repo name and directory verbatim to gh")
step("Verify: exits 0 and forwards the repo name and directory verbatim to gh")
val dir = install_fake_gh(FAKE_GH_PASSTHROUGH_OK)
val (code, log) = run_github_with_fake_gh(dir, ["repo", "clone", "owner/name", "dest"])
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(log.contains("repo clone owner/name dest")).to_equal(true)
```

</details>

#### pr create — passthrough

#### exits 0 and forwards --title/--body/--base verbatim to gh

- exits 0 and forwards --title/--body/--base verbatim to gh
- Verify: exits 0 and forwards --title/--body/--base verbatim to gh
   - Expected: code equals `0`
   - Expected: log contains `pr create --title T --body B --base main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("exits 0 and forwards --title/--body/--base verbatim to gh")
step("Verify: exits 0 and forwards --title/--body/--base verbatim to gh")
val dir = install_fake_gh(FAKE_GH_PASSTHROUGH_OK)
val (code, log) = run_github_with_fake_gh(dir, ["pr", "create", "--title", "T", "--body", "B", "--base", "main"])
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(log.contains("pr create --title T --body B --base main")).to_equal(true)
```

</details>

#### pr review — passthrough

#### exits 0 and forwards the number and review flag verbatim to gh

- exits 0 and forwards the number and review flag verbatim to gh
- Verify: exits 0 and forwards the number and review flag verbatim to gh
   - Expected: code equals `0`
   - Expected: log contains `pr review 42 --approve`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("exits 0 and forwards the number and review flag verbatim to gh")
step("Verify: exits 0 and forwards the number and review flag verbatim to gh")
val dir = install_fake_gh(FAKE_GH_PASSTHROUGH_OK)
val (code, log) = run_github_with_fake_gh(dir, ["pr", "review", "42", "--approve"])
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(log.contains("pr review 42 --approve")).to_equal(true)
```

</details>

#### issue edit — gh unauthenticated

#### exits 1 and surfaces an actionable auth error, not a bare crash

- exits 1 and surfaces an actionable auth error, not a bare crash
- Verify: exits 1 and surfaces an actionable auth error, not a bare crash
   - Expected: code equals `1`
   - Expected: log contains `issue edit 123 --add-label bug`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("exits 1 and surfaces an actionable auth error, not a bare crash")
step("Verify: exits 1 and surfaces an actionable auth error, not a bare crash")
val dir = install_fake_gh(FAKE_GH_UNAUTHED)
val (code, log) = run_github_with_fake_gh(dir, ["issue", "edit", "123", "--add-label", "bug"])
expect(code).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(log.contains("issue edit 123 --add-label bug")).to_equal(true)
```

</details>

#### unknown subcommand

#### exits 1 for an unknown top-level command without touching gh

- exits 1 for an unknown top-level command without touching gh
- Verify: exits 1 for an unknown top-level command without touching gh
   - Expected: handle_github(["bogus"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("exits 1 for an unknown top-level command without touching gh")
step("Verify: exits 1 for an unknown top-level command without touching gh")
expect(handle_github(["bogus"])).to_equal(1)
```

</details>

#### exits 1 for an unknown issue subcommand

- exits 1 for an unknown issue subcommand
- Verify: exits 1 for an unknown issue subcommand
   - Expected: handle_github(["issue", "bogus"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("exits 1 for an unknown issue subcommand")
step("Verify: exits 1 for an unknown issue subcommand")
expect(handle_github(["issue", "bogus"])).to_equal(1)
```

</details>

#### exits 1 for an unknown pr subcommand

- exits 1 for an unknown pr subcommand
- Verify: exits 1 for an unknown pr subcommand
   - Expected: handle_github(["pr", "bogus"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("exits 1 for an unknown pr subcommand")
step("Verify: exits 1 for an unknown pr subcommand")
expect(handle_github(["pr", "bogus"])).to_equal(1)
```

</details>

#### exits 1 for an unknown repo subcommand

- exits 1 for an unknown repo subcommand
- Verify: exits 1 for an unknown repo subcommand
   - Expected: handle_github(["repo", "bogus"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("exits 1 for an unknown repo subcommand")
step("Verify: exits 1 for an unknown repo subcommand")
expect(handle_github(["repo", "bogus"])).to_equal(1)
```

</details>

### cmd_github pure JSON-extraction helpers

#### _gh_field

#### extracts a string field, stripping quotes

- extracts a string field, stripping quotes
- Verify: extracts a string field, stripping quotes
   - Expected: _gh_field(obj, "title") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("extracts a string field, stripping quotes")
step("Verify: extracts a string field, stripping quotes")
val obj = json_parse("{\"title\":\"hello\"}")
expect(_gh_field(obj, "title")).to_equal("hello")
```

</details>

#### extracts a numeric field as text

- extracts a numeric field as text
- Verify: extracts a numeric field as text
   - Expected: _gh_field(obj, "number") equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("extracts a numeric field as text")
step("Verify: extracts a numeric field as text")
val obj = json_parse("{\"number\":42}")
expect(_gh_field(obj, "number")).to_equal("42")
```

</details>

#### returns empty text for a missing field

- returns empty text for a missing field
- Verify: returns empty text for a missing field
   - Expected: _gh_field(obj, "missing") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns empty text for a missing field")
step("Verify: returns empty text for a missing field")
val obj = json_parse("{\"title\":\"hello\"}")
expect(_gh_field(obj, "missing")).to_equal("")
```

</details>

#### _gh_login

#### extracts the nested login field gh uses for author/assignee

- extracts the nested login field gh uses for author/assignee
- Verify: extracts the nested login field gh uses for author/assignee
   - Expected: _gh_login(obj, "author") equals `alice`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("extracts the nested login field gh uses for author/assignee")
step("Verify: extracts the nested login field gh uses for author/assignee")
# NOTE: braces must be doubled ({{/}}) here even though this is a
# plain val, not a print — Simple's string-interpolation scanner
# treats bare `{`/`}` as interpolation delimiters in ANY string
# literal once they're nested two levels deep (a single flat
# `{"a":"b"}` literal is tolerated as-is, as the other _gh_field
# cases above show, but `{"a":{"b":"c"}}` is not — found while
# writing this spec; compiler quirk, reported, not fixed here).
val obj = json_parse("{{\"author\":{{\"login\":\"alice\"}}}}")
expect(_gh_login(obj, "author")).to_equal("alice")
```

</details>

#### returns empty text when the nested object is absent

- returns empty text when the nested object is absent
- Verify: returns empty text when the nested object is absent
   - Expected: _gh_login(obj, "author") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns empty text when the nested object is absent")
step("Verify: returns empty text when the nested object is absent")
val obj = json_parse("{}")
expect(_gh_login(obj, "author")).to_equal("")
```

</details>

#### _default_fields

#### uses the pr field set (includes headRefName) for entity=pr

- uses the pr field set (includes headRefName) for entity=pr
- Verify: uses the pr field set (includes headRefName) for entity=pr
   - Expected: _default_fields("pr") equals `number,title,state,author,headRefName,updatedAt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("uses the pr field set (includes headRefName) for entity=pr")
step("Verify: uses the pr field set (includes headRefName) for entity=pr")
expect(_default_fields("pr")).to_equal("number,title,state,author,headRefName,updatedAt")
```

</details>

#### uses the issue field set for entity=issue

- uses the issue field set for entity=issue
- Verify: uses the issue field set for entity=issue
   - Expected: _default_fields("issue") equals `number,title,state,author,updatedAt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("uses the issue field set for entity=issue")
step("Verify: uses the issue field set for entity=issue")
expect(_default_fields("issue")).to_equal("number,title,state,author,updatedAt")
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

- `REQ-SSPEC-APP`
- `REQ-APP-DEVHUB-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d2f3eac4405558bd28ae21ae3ac3db15a82866c758cc73c06b5fc2d2c0bfdb87`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d2f3eac4405558bd28ae21ae3ac3db15a82866c758cc73c06b5fc2d2c0bfdb87`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d2f3eac4405558bd28ae21ae3ac3db15a82866c758cc73c06b5fc2d2c0bfdb87`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/app/devhub/cmd_github_spec.spl
mirror: doc/06_spec/01_unit/app/devhub/cmd_github_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/devhub/cmd_github_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/devhub/cmd_github_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/devhub/cmd_github_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/devhub/cmd_github_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exits 0 and forwards the default --json fields to gh' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/devhub/cmd_github_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'forwards extra gh-native flags (e.g. --state, --limit) verbatim' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/devhub/cmd_github_spec.spl:113:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exits 0 on an empty array (no issues/PRs is not an error)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
