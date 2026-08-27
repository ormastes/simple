# cmd_github_spec

> Purpose: Prove that itf github (fake-binary fixture).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

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
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that itf github (fake-binary fixture).
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### itf github (fake-binary fixture)

#### issue list — success path

#### exits 0 and forwards the default --json fields to gh

- Verify: exits 0 and forwards the default --json fields to gh
   - Expected: code equals `0`
   - Expected: log contains `issue list --json number,title,state,author,updatedAt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: exits 0 and forwards the default --json fields to gh")
# @req: REQ-APP-DEVHUB-001
val dir = install_fake_gh(FAKE_GH_LIST_OK)
val (code, log) = run_github_with_fake_gh(dir, ["issue", "list"])
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(log.contains("issue list --json number,title,state,author,updatedAt")).to_equal(true)
```

</details>

#### forwards extra gh-native flags (e.g. --state, --limit) verbatim

- Verify: forwards extra gh-native flags (e.g. --state, --limit) verbatim
   - Expected: code equals `0`
   - Expected: log contains `--state open --limit 5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: forwards extra gh-native flags (e.g. --state, --limit) verbatim")
val dir = install_fake_gh(FAKE_GH_LIST_OK)
val (code, log) = run_github_with_fake_gh(dir, ["issue", "list", "--state", "open", "--limit", "5"])
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(log.contains("--state open --limit 5")).to_equal(true)
```

</details>

#### pr list — empty result

#### exits 0 on an empty array (no issues/PRs is not an error)

- Verify: exits 0 on an empty array (no issues/PRs is not an error)
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: exits 0 on an empty array (no issues/PRs is not an error)")
val dir = install_fake_gh(FAKE_GH_LIST_OK)
val (code, _log) = run_github_with_fake_gh(dir, ["pr", "list"])
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### gh missing

#### exits 1 with an actionable 'not found' error (never a bare crash)

- Verify: exits 1 with an actionable 'not found' error (never a bare crash)
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: exits 1 with an actionable 'not found' error (never a bare crash)")
val dir = install_fake_gh(FAKE_GH_NOT_FOUND)
val (code, _log) = run_github_with_fake_gh(dir, ["issue", "list"])
expect(code).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### gh unauthenticated

#### exits 1 and does not fall through to a bare exit code

- Verify: exits 1 and does not fall through to a bare exit code
   - Expected: code equals `1`
   - Expected: log contains `issue list`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: exits 1 and does not fall through to a bare exit code")
val dir = install_fake_gh(FAKE_GH_UNAUTHED)
val (code, log) = run_github_with_fake_gh(dir, ["issue", "list"])
expect(code).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(log.contains("issue list")).to_equal(true)
```

</details>

#### issue edit — passthrough

#### exits 0 and forwards the number and flags verbatim to gh

- Verify: exits 0 and forwards the number and flags verbatim to gh
   - Expected: code equals `0`
   - Expected: log contains `issue edit 123 --add-label bug`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: exits 0 and forwards the number and flags verbatim to gh")
val dir = install_fake_gh(FAKE_GH_PASSTHROUGH_OK)
val (code, log) = run_github_with_fake_gh(dir, ["issue", "edit", "123", "--add-label", "bug"])
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(log.contains("issue edit 123 --add-label bug")).to_equal(true)
```

</details>

#### repo clone — passthrough

#### exits 0 and forwards the repo name and directory verbatim to gh

- Verify: exits 0 and forwards the repo name and directory verbatim to gh
   - Expected: code equals `0`
   - Expected: log contains `repo clone owner/name dest`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: exits 0 and forwards the repo name and directory verbatim to gh")
val dir = install_fake_gh(FAKE_GH_PASSTHROUGH_OK)
val (code, log) = run_github_with_fake_gh(dir, ["repo", "clone", "owner/name", "dest"])
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(log.contains("repo clone owner/name dest")).to_equal(true)
```

</details>

#### pr create — passthrough

#### exits 0 and forwards --title/--body/--base verbatim to gh

- Verify: exits 0 and forwards --title/--body/--base verbatim to gh
   - Expected: code equals `0`
   - Expected: log contains `pr create --title T --body B --base main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: exits 0 and forwards --title/--body/--base verbatim to gh")
val dir = install_fake_gh(FAKE_GH_PASSTHROUGH_OK)
val (code, log) = run_github_with_fake_gh(dir, ["pr", "create", "--title", "T", "--body", "B", "--base", "main"])
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(log.contains("pr create --title T --body B --base main")).to_equal(true)
```

</details>

#### pr review — protected self-review redirect

#### detects the same author before provider approval and does not submit APPROVED

- Verify: detects the same author before provider approval and does not submit APPROVED
   - Expected: code equals `2`
   - Expected: log contains `pr view 42 --json number,author`
   - Expected: log does not contain `pr review 42 --approve`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: detects the same author before provider approval and does not submit APPROVED")
val dir = install_fake_gh(FAKE_GH_SAME_AUTHOR)
val (code, log) = run_github_with_fake_gh(dir, ["pr", "review", "42", "--approve"])
expect(code).to_equal(2)
expect(log.contains("pr view 42 --json number,author")).to_equal(true)
expect(log.contains("pr review 42 --approve")).to_equal(false)
```

</details>

#### recognizes -a and resolves an omitted selector from the current branch

- Verify: recognizes -a and resolves an omitted selector from the current branch
   - Expected: code equals `2`
   - Expected: log contains `pr view --json number,author`
   - Expected: log does not contain `pr review -a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: recognizes -a and resolves an omitted selector from the current branch")
val dir = install_fake_gh(FAKE_GH_SAME_AUTHOR)
val (code, log) = run_github_with_fake_gh(dir, ["pr", "review", "-a"])
expect(code).to_equal(2)
expect(log.contains("pr view --json number,author")).to_equal(true)
expect(log.contains("pr review -a")).to_equal(false)
```

</details>

#### resolves a URL selector and uses the returned PR number

- Verify: resolves a URL selector and uses the returned PR number
   - Expected: code equals `2`
   - Expected: log contains `pr view https://github.com/ormastes/simple/pull/42 --json number,author`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: resolves a URL selector and uses the returned PR number")
val dir = install_fake_gh(FAKE_GH_SAME_AUTHOR)
val (code, log) = run_github_with_fake_gh(dir, ["pr", "review", "https://github.com/ormastes/simple/pull/42", "--approve"])
expect(code).to_equal(2)
expect(log.contains("pr view https://github.com/ormastes/simple/pull/42 --json number,author")).to_equal(true)
```

</details>

#### prints the same workflow after GitHub rejects author approval

- Verify: prints the same workflow after GitHub rejects author approval
   - Expected: code equals `1`
   - Expected: log contains `pr review 42 --approve`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: prints the same workflow after GitHub rejects author approval")
val dir = install_fake_gh(FAKE_GH_AUTHOR_REJECTION)
val (code, log) = run_github_with_fake_gh(dir, ["pr", "review", "42", "--approve"])
expect(code).to_equal(1)
expect(log.contains("pr review 42 --approve")).to_equal(true)
```

</details>

#### issue edit — gh unauthenticated

#### exits 1 and surfaces an actionable auth error, not a bare crash

- Verify: exits 1 and surfaces an actionable auth error, not a bare crash
   - Expected: code equals `1`
   - Expected: log contains `issue edit 123 --add-label bug`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: exits 1 and surfaces an actionable auth error, not a bare crash")
val dir = install_fake_gh(FAKE_GH_UNAUTHED)
val (code, log) = run_github_with_fake_gh(dir, ["issue", "edit", "123", "--add-label", "bug"])
expect(code).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(log.contains("issue edit 123 --add-label bug")).to_equal(true)
```

</details>

#### unknown subcommand

#### exits 1 for an unknown top-level command without touching gh

- Verify: exits 1 for an unknown top-level command without touching gh
   - Expected: handle_github(["bogus"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: exits 1 for an unknown top-level command without touching gh")
expect(handle_github(["bogus"])).to_equal(1)
```

</details>

#### exits 1 for an unknown issue subcommand

- Verify: exits 1 for an unknown issue subcommand
   - Expected: handle_github(["issue", "bogus"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: exits 1 for an unknown issue subcommand")
expect(handle_github(["issue", "bogus"])).to_equal(1)
```

</details>

#### exits 1 for an unknown pr subcommand

- Verify: exits 1 for an unknown pr subcommand
   - Expected: handle_github(["pr", "bogus"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: exits 1 for an unknown pr subcommand")
expect(handle_github(["pr", "bogus"])).to_equal(1)
```

</details>

#### exits 1 for an unknown repo subcommand

- Verify: exits 1 for an unknown repo subcommand
   - Expected: handle_github(["repo", "bogus"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: exits 1 for an unknown repo subcommand")
expect(handle_github(["repo", "bogus"])).to_equal(1)
```

</details>

### cmd_github pure JSON-extraction helpers

#### self-review discoverability

#### recognizes provider author-approval rejection variants

- Verify: recognizes provider author-approval rejection variants


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: recognizes provider author-approval rejection variants")
expect(_github_author_approval_rejected("cannot approve your own pull request")).to_be(true)
expect(_github_author_approval_rejected("ordinary validation error")).to_be(false)
```

</details>

#### exposes exact review dispatch poll steps for common agent searches

- Verify: exposes exact review dispatch poll steps for common agent searches


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: exposes exact review dispatch poll steps for common agent searches")
val steps = _self_review_steps("42")
expect(steps[0]).to_contain("APPROVED")
expect(steps[1]).to_contain("--repo ormastes/simple")
expect(steps[2]).to_contain("high/xhigh/max/ultra")
expect(steps[3]).to_contain("P0=0")
expect(steps[5]).to_contain("pull_request_number=42")
expect(steps[5]).to_contain("self_attestation='PASS:0:0'")
expect(steps[6]).to_contain("$HEAD_SHA")
expect(steps[7]).to_contain("evaluate privilege first")
expect(steps[8]).to_contain("not GitHub provider APPROVED")
expect(steps[9]).to_contain("spipe self-review-guide")
```

</details>

#### _gh_field

#### extracts a string field, stripping quotes

- Verify: extracts a string field, stripping quotes
   - Expected: _gh_field(obj, "title") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: extracts a string field, stripping quotes")
val obj = json_parse("{\"title\":\"hello\"}")
expect(_gh_field(obj, "title")).to_equal("hello")
```

</details>

#### extracts a numeric field as text

- Verify: extracts a numeric field as text
   - Expected: _gh_field(obj, "number") equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: extracts a numeric field as text")
val obj = json_parse("{\"number\":42}")
expect(_gh_field(obj, "number")).to_equal("42")
```

</details>

#### returns empty text for a missing field

- Verify: returns empty text for a missing field
   - Expected: _gh_field(obj, "missing") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: returns empty text for a missing field")
val obj = json_parse("{\"title\":\"hello\"}")
expect(_gh_field(obj, "missing")).to_equal("")
```

</details>

#### _gh_login

#### extracts the nested login field gh uses for author/assignee

- Verify: extracts the nested login field gh uses for author/assignee
   - Expected: _gh_login(obj, "author") equals `alice`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Verify: returns empty text when the nested object is absent
   - Expected: _gh_login(obj, "author") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: returns empty text when the nested object is absent")
val obj = json_parse("{}")
expect(_gh_login(obj, "author")).to_equal("")
```

</details>

#### _default_fields

#### uses the pr field set (includes headRefName) for entity=pr

- Verify: uses the pr field set (includes headRefName) for entity=pr
   - Expected: _default_fields("pr") equals `number,title,state,author,headRefName,updatedAt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: uses the pr field set (includes headRefName) for entity=pr")
expect(_default_fields("pr")).to_equal("number,title,state,author,headRefName,updatedAt")
```

</details>

#### uses the issue field set for entity=issue

- Verify: uses the issue field set for entity=issue
   - Expected: _default_fields("issue") equals `number,title,state,author,updatedAt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: uses the issue field set for entity=issue")
expect(_default_fields("issue")).to_equal("number,title,state,author,updatedAt")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
