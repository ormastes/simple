# cmd_tasks_spec

> Purpose: Prove that cmd_tasks pure helpers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 54 | 54 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# cmd_tasks_spec

Purpose: Prove that cmd_tasks pure helpers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/devhub/cmd_tasks_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that cmd_tasks pure helpers.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### cmd_tasks pure helpers

#### _jira_build_list_jql (G1 — D2/D3/D4 synthesis)

#### golden case: @me assignee synthesizes currentUser(), default open state

- golden case: @me assignee synthesizes currentUser(), default open state
- Verify: golden case: @me assignee synthesizes currentUser(), default open state
   - Expected: _jira_build_list_jql("@me", "", "open", "") equals `assignee = currentUser() AND statusCategory != Done`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("golden case: @me assignee synthesizes currentUser(), default open state")
step("Verify: golden case: @me assignee synthesizes currentUser(), default open state")
# @req: REQ-APP-DEVHUB-001
expect(_jira_build_list_jql("@me", "", "open", "")).to_equal("assignee = currentUser() AND statusCategory != Done")
```

</details>

#### a literal (non-@me) assignee becomes a quoted JQL literal

- a literal (non-@me) assignee becomes a quoted JQL literal
- Verify: a literal (non-@me) assignee becomes a quoted JQL literal
   - Expected: _jira_build_list_jql("alice", "", "", "") equals `assignee = "alice"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("a literal (non-@me) assignee becomes a quoted JQL literal")
step("Verify: a literal (non-@me) assignee becomes a quoted JQL literal")
expect(_jira_build_list_jql("alice", "", "", "")).to_equal("assignee = \"alice\"")
```

</details>

#### label filter

- label filter
- Verify: label filter
   - Expected: _jira_build_list_jql("", "bug", "", "") equals `labels = "bug"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("label filter")
step("Verify: label filter")
expect(_jira_build_list_jql("", "bug", "", "")).to_equal("labels = \"bug\"")
```

</details>

#### state=closed maps to statusCategory = Done

- state=closed maps to statusCategory = Done
- Verify: state=closed maps to statusCategory = Done
   - Expected: _jira_build_list_jql("", "", "closed", "") equals `statusCategory = Done`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("state=closed maps to statusCategory = Done")
step("Verify: state=closed maps to statusCategory = Done")
expect(_jira_build_list_jql("", "", "closed", "")).to_equal("statusCategory = Done")
```

</details>

#### state=all omits the statusCategory clause entirely

- state=all omits the statusCategory clause entirely
- Verify: state=all omits the statusCategory clause entirely
   - Expected: _jira_build_list_jql("", "", "all", "") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("state=all omits the statusCategory clause entirely")
step("Verify: state=all omits the statusCategory clause entirely")
expect(_jira_build_list_jql("", "", "all", "")).to_equal("")
```

</details>

#### search text becomes a JQL text ~ clause

- search text becomes a JQL text ~ clause
- Verify: search text becomes a JQL text ~ clause
   - Expected: _jira_build_list_jql("", "", "", "urgent") equals `text ~ "urgent"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("search text becomes a JQL text ~ clause")
step("Verify: search text becomes a JQL text ~ clause")
expect(_jira_build_list_jql("", "", "", "urgent")).to_equal("text ~ \"urgent\"")
```

</details>

#### combines multiple filters with AND, in assignee/label/state/search order

- combines multiple filters with AND, in assignee/label/state/search order
- Verify: combines multiple filters with AND, in assignee/label/state/search order
   - Expected: _jira_build_list_jql("@me", "bug", "open", "urgent") equals `assignee = currentUser() AND labels = "bug" AND statusCategory != Done AND te... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("combines multiple filters with AND, in assignee/label/state/search order")
step("Verify: combines multiple filters with AND, in assignee/label/state/search order")
expect(_jira_build_list_jql("@me", "bug", "open", "urgent")).to_equal("assignee = currentUser() AND labels = \"bug\" AND statusCategory != Done AND text ~ \"urgent\"")
```

</details>

#### no filters at all yields an empty JQL string

- no filters at all yields an empty JQL string
- Verify: no filters at all yields an empty JQL string
   - Expected: _jira_build_list_jql("", "", "", "") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("no filters at all yields an empty JQL string")
step("Verify: no filters at all yields an empty JQL string")
expect(_jira_build_list_jql("", "", "", "")).to_equal("")
```

</details>

#### _looks_like_jira_key (backend auto-detect from id shape)

#### recognizes a standard jira key

- recognizes a standard jira key
- Verify: recognizes a standard jira key
   - Expected: _looks_like_jira_key("PROJ-123") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("recognizes a standard jira key")
step("Verify: recognizes a standard jira key")
expect(_looks_like_jira_key("PROJ-123")).to_equal(true)
```

</details>

#### rejects a bare github issue number

- rejects a bare github issue number
- Verify: rejects a bare github issue number
   - Expected: _looks_like_jira_key("123") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects a bare github issue number")
step("Verify: rejects a bare github issue number")
expect(_looks_like_jira_key("123")).to_equal(false)
```

</details>

#### rejects a lowercase prefix

- rejects a lowercase prefix
- Verify: rejects a lowercase prefix
   - Expected: _looks_like_jira_key("proj-123") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects a lowercase prefix")
step("Verify: rejects a lowercase prefix")
expect(_looks_like_jira_key("proj-123")).to_equal(false)
```

</details>

#### rejects a non-numeric suffix

- rejects a non-numeric suffix
- Verify: rejects a non-numeric suffix
   - Expected: _looks_like_jira_key("PROJ-abc") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects a non-numeric suffix")
step("Verify: rejects a non-numeric suffix")
expect(_looks_like_jira_key("PROJ-abc")).to_equal(false)
```

</details>

#### rejects a missing suffix

- rejects a missing suffix
- Verify: rejects a missing suffix
   - Expected: _looks_like_jira_key("PROJ-") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects a missing suffix")
step("Verify: rejects a missing suffix")
expect(_looks_like_jira_key("PROJ-")).to_equal(false)
```

</details>

#### _parse_limit

#### parses a plain decimal string

- parses a plain decimal string
- Verify: parses a plain decimal string
   - Expected: _parse_limit("10", 30) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("parses a plain decimal string")
step("Verify: parses a plain decimal string")
expect(_parse_limit("10", 30)).to_equal(10)
```

</details>

#### falls back to the default on empty input

- falls back to the default on empty input
- Verify: falls back to the default on empty input
   - Expected: _parse_limit("", 30) equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("falls back to the default on empty input")
step("Verify: falls back to the default on empty input")
expect(_parse_limit("", 30)).to_equal(30)
```

</details>

#### falls back to the default on non-digit input

- falls back to the default on non-digit input
- Verify: falls back to the default on non-digit input
   - Expected: _parse_limit("abc", 30) equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("falls back to the default on non-digit input")
step("Verify: falls back to the default on non-digit input")
expect(_parse_limit("abc", 30)).to_equal(30)
```

</details>

#### falls back to the default on a leading-negative sign

- falls back to the default on a leading-negative sign
- Verify: falls back to the default on a leading-negative sign
   - Expected: _parse_limit("-5", 30) equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("falls back to the default on a leading-negative sign")
step("Verify: falls back to the default on a leading-negative sign")
expect(_parse_limit("-5", 30)).to_equal(30)
```

</details>

#### _tasks_github_rows_from_json (D6 merge row extraction)

#### extracts number/state/author/title/updated from a one-item gh --json array

- extracts number/state/author/title/updated from a one-item gh --json array
- Verify: extracts number/state/author/title/updated from a one-item gh --json array
   - Expected: rows.len() equals `1`
   - Expected: rows[0][0] equals `#42`
   - Expected: rows[0][2] equals `alice`
   - Expected: rows[0][3] equals `fixture issue`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("extracts number/state/author/title/updated from a one-item gh --json array")
step("Verify: extracts number/state/author/title/updated from a one-item gh --json array")
# NOTE: braces doubled ({{/}}) per cmd_github_spec.spl's nested-JSON
# literal rule (a single flat `{"a":"b"}` is fine, but nesting two
# levels deep like `{"a":{"b":"c"}}` needs doubling).
val raw = "[{{\"number\":42,\"title\":\"fixture issue\",\"state\":\"OPEN\",\"author\":{{\"login\":\"alice\"}},\"updatedAt\":\"2026-07-01T00:00:00Z\"}}]"
val rows = _tasks_github_rows_from_json(raw)
expect(rows.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(rows[0][0]).to_equal("#42")
expect(rows[0][2]).to_equal("alice")
expect(rows[0][3]).to_equal("fixture issue")
```

</details>

#### returns an empty row list for a non-array payload

- returns an empty row list for a non-array payload
- Verify: returns an empty row list for a non-array payload
   - Expected: _tasks_github_rows_from_json("{{\"not\":\"an array\"}}").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns an empty row list for a non-array payload")
step("Verify: returns an empty row list for a non-array payload")
expect(_tasks_github_rows_from_json("{{\"not\":\"an array\"}}").len()).to_equal(0)
```

</details>

#### _strip_first_positional (search -> list --search delegation)

#### removes only the first bare positional, keeping flag+value pairs

- removes only the first bare positional, keeping flag+value pairs
- Verify: removes only the first bare positional, keeping flag+value pairs
   - Expected: _strip_first_positional(["urgent", "--backend", "github"]) equals `["--backend", "github"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("removes only the first bare positional, keeping flag+value pairs")
step("Verify: removes only the first bare positional, keeping flag+value pairs")
expect(_strip_first_positional(["urgent", "--backend", "github"])).to_equal(["--backend", "github"])
```

</details>

#### keeps a second positional if present

- keeps a second positional if present
- Verify: keeps a second positional if present
   - Expected: _strip_first_positional(["urgent", "--backend", "github", "extra"]) equals `["--backend", "github", "extra"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps a second positional if present")
step("Verify: keeps a second positional if present")
expect(_strip_first_positional(["urgent", "--backend", "github", "extra"])).to_equal(["--backend", "github", "extra"])
```

</details>

#### returns an empty array unchanged

- returns an empty array unchanged
- Verify: returns an empty array unchanged
   - Expected: _strip_first_positional([]) equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns an empty array unchanged")
step("Verify: returns an empty array unchanged")
expect(_strip_first_positional([])).to_equal([])
```

</details>

### itf tasks (fake-binary fixture)

#### list — github backend

#### exits 0 and forwards default --json fields to gh

- exits 0 and forwards default --json fields to gh
- Verify: exits 0 and forwards default --json fields to gh
   - Expected: code equals `0`
   - Expected: log contains `issue list --json number,title,state,author,updatedAt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("exits 0 and forwards default --json fields to gh")
step("Verify: exits 0 and forwards default --json fields to gh")
reset_fixture()
clear_fixture_config()
install_fake_bin("gh", FAKE_GH_OK)
val (code, log) = run_tasks(["list", "--backend", "github"])
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(log.contains("issue list --json number,title,state,author,updatedAt")).to_equal(true)
```

</details>

#### passes --assignee/--label/--state/--search/--limit through to gh verbatim (D2/D4)

- passes --assignee/--label/--state/--search/--limit through to gh verbatim (D2/D4)
- Verify: passes --assignee/--label/--state/--search/--limit through to gh verbatim (D2/D4)
   - Expected: code equals `0`
   - Expected: log contains `--assignee @me`
   - Expected: log contains `--state closed`
   - Expected: log contains `--label bug`
   - Expected: log contains `--search urgent`
   - Expected: log contains `--limit 5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("passes --assignee/--label/--state/--search/--limit through to gh verbatim (D2/D4)")
step("Verify: passes --assignee/--label/--state/--search/--limit through to gh verbatim (D2/D4)")
reset_fixture()
clear_fixture_config()
install_fake_bin("gh", FAKE_GH_OK)
val (code, log) = run_tasks(["list", "--backend", "github", "--assignee", "@me", "--state", "closed", "--label", "bug", "--search", "urgent", "--limit", "5"])
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(log.contains("--assignee @me")).to_equal(true)
expect(log.contains("--state closed")).to_equal(true)
expect(log.contains("--label bug")).to_equal(true)
expect(log.contains("--search urgent")).to_equal(true)
expect(log.contains("--limit 5")).to_equal(true)
```

</details>

#### list — jira backend

#### exits 0 and synthesizes a JQL query passed to acli --jql

- exits 0 and synthesizes a JQL query passed to acli --jql
- Verify: exits 0 and synthesizes a JQL query passed to acli --jql
   - Expected: code equals `0`
   - Expected: log contains `--jql statusCategory != Done`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("exits 0 and synthesizes a JQL query passed to acli --jql")
step("Verify: exits 0 and synthesizes a JQL query passed to acli --jql")
reset_fixture()
clear_fixture_config()
install_fake_bin("acli", FAKE_ACLI_OK)
val (code, log) = run_tasks(["list", "--backend", "jira", "--state", "open"])
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(log.contains("--jql statusCategory != Done")).to_equal(true)
```

</details>

#### @me golden path: --assignee @me reaches acli as currentUser()

- @me golden path: --assignee @me reaches acli as currentUser()
- Verify: @me golden path: --assignee @me reaches acli as currentUser()
   - Expected: code equals `0`
   - Expected: log contains `currentUser()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("@me golden path: --assignee @me reaches acli as currentUser()")
step("Verify: @me golden path: --assignee @me reaches acli as currentUser()")
reset_fixture()
clear_fixture_config()
install_fake_bin("acli", FAKE_ACLI_OK)
val (code, log) = run_tasks(["list", "--backend", "jira", "--assignee", "@me"])
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(log.contains("currentUser()")).to_equal(true)
```

</details>

#### list — --backend all (D6 merge)

#### queries both backends, merges non-empty rows, and exits 0

- queries both backends, merges non-empty rows, and exits 0
- Verify: queries both backends, merges non-empty rows, and exits 0
   - Expected: code equals `0`
   - Expected: log contains `issue list`
   - Expected: log contains `jira workitem search`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("queries both backends, merges non-empty rows, and exits 0")
step("Verify: queries both backends, merges non-empty rows, and exits 0")
reset_fixture()
clear_fixture_config()
install_fake_bin("gh", FAKE_GH_LIST_ONE)
install_fake_bin("acli", FAKE_ACLI_SEARCH_ONE)
val (code, log) = run_tasks(["list", "--backend", "all"])
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(log.contains("issue list")).to_equal(true)
expect(log.contains("jira workitem search")).to_equal(true)
```

</details>

#### partial failure: github missing, jira succeeds -> still exits 0

- partial failure: github missing, jira succeeds -> still exits 0
- Verify: partial failure: github missing, jira succeeds -> still exits 0
   - Expected: code equals `0`
   - Expected: log contains `jira workitem search`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("partial failure: github missing, jira succeeds -> still exits 0")
step("Verify: partial failure: github missing, jira succeeds -> still exits 0")
reset_fixture()
clear_fixture_config()
install_fake_bin("gh", FAKE_GH_NOT_FOUND)
install_fake_bin("acli", FAKE_ACLI_OK)
val (code, log) = run_tasks(["list", "--backend", "all"])
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(log.contains("jira workitem search")).to_equal(true)
```

</details>

#### both backends fail -> exits 1

- both backends fail -> exits 1
- Verify: both backends fail -> exits 1
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("both backends fail -> exits 1")
step("Verify: both backends fail -> exits 1")
reset_fixture()
clear_fixture_config()
install_fake_bin("gh", FAKE_GH_NOT_FOUND)
install_fake_bin("acli", FAKE_ACLI_FAIL)
val (code, _log) = run_tasks(["list", "--backend", "all"])
expect(code).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### search — thin alias for list --search

#### github: promotes the positional query into --search

- github: promotes the positional query into --search
- Verify: github: promotes the positional query into --search
   - Expected: code equals `0`
   - Expected: log contains `--search urgent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("github: promotes the positional query into --search")
step("Verify: github: promotes the positional query into --search")
reset_fixture()
clear_fixture_config()
install_fake_bin("gh", FAKE_GH_OK)
val (code, log) = run_tasks(["search", "urgent", "--backend", "github"])
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(log.contains("--search urgent")).to_equal(true)
```

</details>

#### exits 1 when no query is given

- exits 1 when no query is given
- Verify: exits 1 when no query is given
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("exits 1 when no query is given")
step("Verify: exits 1 when no query is given")
reset_fixture()
clear_fixture_config()
val (code, _log) = run_tasks(["search", "--backend", "github"])
expect(code).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### view — backend auto-detect from id shape

#### a PROJ-123-shaped id routes to jira even with no --backend flag

- a PROJ-123-shaped id routes to jira even with no --backend flag
- Verify: a PROJ-123-shaped id routes to jira even with no --backend flag
   - Expected: code equals `0`
   - Expected: log contains `jira workitem view PROJ-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("a PROJ-123-shaped id routes to jira even with no --backend flag")
step("Verify: a PROJ-123-shaped id routes to jira even with no --backend flag")
reset_fixture()
clear_fixture_config()
install_fake_bin("acli", FAKE_ACLI_OK)
val (code, log) = run_tasks(["view", "PROJ-1"])
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(log.contains("jira workitem view PROJ-1")).to_equal(true)
```

</details>

#### a bare number with configured tasks:default_backend=github routes to gh

- a bare number with configured tasks:default_backend=github routes to gh
- Verify: a bare number with configured tasks:default_backend=github routes to gh
   - Expected: code equals `0`
   - Expected: log contains `issue view 42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("a bare number with configured tasks:default_backend=github routes to gh")
step("Verify: a bare number with configured tasks:default_backend=github routes to gh")
reset_fixture()
clear_fixture_config()
write_fixture_config("github", "", "", "", "")
install_fake_bin("gh", FAKE_GH_OK)
val (code, log) = run_tasks(["view", "42"])
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(log.contains("issue view 42")).to_equal(true)
```

</details>

#### D1: an explicit --backend flag overrides a configured tasks:default_backend

- D1: an explicit --backend flag overrides a configured tasks:default_backend
- Verify: D1: an explicit --backend flag overrides a configured tasks:default_backend
   - Expected: code equals `0`
   - Expected: log contains `jira workitem view 42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("D1: an explicit --backend flag overrides a configured tasks:default_backend")
step("Verify: D1: an explicit --backend flag overrides a configured tasks:default_backend")
# Uses a bare number (not a PROJ-123-shaped id) so id-shape
# auto-detection can't also explain a jira result: config
# default is "github" here, so only an honored --backend flag
# routes this to jira (an ignored flag would fall through to
# "42" -> not jira-shaped -> configured "github" -> gh, which
# isn't installed in this fixture and would fail).
reset_fixture()
clear_fixture_config()
write_fixture_config("github", "", "", "", "")
install_fake_bin("acli", FAKE_ACLI_OK)
val (code, log) = run_tasks(["view", "42", "--backend", "jira"])
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(log.contains("jira workitem view 42")).to_equal(true)
```

</details>

#### --backend all is rejected for a single-item verb

- --backend all is rejected for a single-item verb
- Verify: --backend all is rejected for a single-item verb
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("--backend all is rejected for a single-item verb")
step("Verify: --backend all is rejected for a single-item verb")
reset_fixture()
clear_fixture_config()
val (code, _log) = run_tasks(["view", "PROJ-1", "--backend", "all"])
expect(code).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### create

#### github: requires --title

- github: requires --title
- Verify: github: requires --title
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("github: requires --title")
step("Verify: github: requires --title")
reset_fixture()
clear_fixture_config()
val (code, _log) = run_tasks(["create", "--backend", "github", "--body", "B"])
expect(code).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### github: forwards --title/--body to gh

- github: forwards --title/--body to gh
- Verify: github: forwards --title/--body to gh
   - Expected: code equals `0`
   - Expected: log contains `issue create --title T --body B`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("github: forwards --title/--body to gh")
step("Verify: github: forwards --title/--body to gh")
reset_fixture()
clear_fixture_config()
install_fake_bin("gh", FAKE_GH_OK)
val (code, log) = run_tasks(["create", "--backend", "github", "--title", "T", "--body", "B"])
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(log.contains("issue create --title T --body B")).to_equal(true)
```

</details>

#### jira: requires --project

- jira: requires --project
- Verify: jira: requires --project
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("jira: requires --project")
step("Verify: jira: requires --project")
reset_fixture()
clear_fixture_config()
install_fake_bin("acli", FAKE_ACLI_OK)
val (code, _log) = run_tasks(["create", "--backend", "jira", "--title", "T"])
expect(code).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### jira: --title translates to --summary for acli

- jira: --title translates to --summary for acli
- Verify: jira: --title translates to --summary for acli
   - Expected: code equals `0`
   - Expected: log contains `jira workitem create --project PROJ --summary New bug`
   - Expected: log contains `--description desc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("jira: --title translates to --summary for acli")
step("Verify: jira: --title translates to --summary for acli")
reset_fixture()
clear_fixture_config()
install_fake_bin("acli", FAKE_ACLI_OK)
val (code, log) = run_tasks(["create", "--backend", "jira", "--project", "PROJ", "--title", "New bug", "--body", "desc"])
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(log.contains("jira workitem create --project PROJ --summary New bug")).to_equal(true)
expect(log.contains("--description desc")).to_equal(true)
```

</details>

#### comment

#### requires --body regardless of backend

- requires --body regardless of backend
- Verify: requires --body regardless of backend
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("requires --body regardless of backend")
step("Verify: requires --body regardless of backend")
reset_fixture()
clear_fixture_config()
val (code, _log) = run_tasks(["comment", "42", "--backend", "github"])
expect(code).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### github: forwards id + --body to gh

- github: forwards id + --body to gh
- Verify: github: forwards id + --body to gh
   - Expected: code equals `0`
   - Expected: log contains `issue comment 42 --body hi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("github: forwards id + --body to gh")
step("Verify: github: forwards id + --body to gh")
reset_fixture()
clear_fixture_config()
install_fake_bin("gh", FAKE_GH_OK)
val (code, log) = run_tasks(["comment", "42", "--backend", "github", "--body", "hi"])
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(log.contains("issue comment 42 --body hi")).to_equal(true)
```

</details>

#### jira: forwards id + --body to acli

- jira: forwards id + --body to acli
- Verify: jira: forwards id + --body to acli
   - Expected: code equals `0`
   - Expected: log contains `jira workitem comment PROJ-1 --body status update`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("jira: forwards id + --body to acli")
step("Verify: jira: forwards id + --body to acli")
reset_fixture()
clear_fixture_config()
install_fake_bin("acli", FAKE_ACLI_OK)
val (code, log) = run_tasks(["comment", "PROJ-1", "--backend", "jira", "--body", "status update"])
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(log.contains("jira workitem comment PROJ-1 --body status update")).to_equal(true)
```

</details>

#### close (D5 — jira transitions to a configured done-status)

#### github: passthrough to gh issue close

- github: passthrough to gh issue close
- Verify: github: passthrough to gh issue close
   - Expected: code equals `0`
   - Expected: log contains `issue close 42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("github: passthrough to gh issue close")
step("Verify: github: passthrough to gh issue close")
reset_fixture()
clear_fixture_config()
install_fake_bin("gh", FAKE_GH_OK)
val (code, log) = run_tasks(["close", "42", "--backend", "github"])
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(log.contains("issue close 42")).to_equal(true)
```

</details>

#### jira: transitions to the default 'Done' status when unconfigured

- jira: transitions to the default 'Done' status when unconfigured
- Verify: jira: transitions to the default 'Done' status when unconfigured
   - Expected: code equals `0`
   - Expected: log contains `jira workitem transition PROJ-1 --status Done`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("jira: transitions to the default 'Done' status when unconfigured")
step("Verify: jira: transitions to the default 'Done' status when unconfigured")
reset_fixture()
clear_fixture_config()
install_fake_bin("acli", FAKE_ACLI_OK)
val (code, log) = run_tasks(["close", "PROJ-1", "--backend", "jira"])
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(log.contains("jira workitem transition PROJ-1 --status Done")).to_equal(true)
```

</details>

#### jira: honors a configured tasks:jira_done_status override

- jira: honors a configured tasks:jira_done_status override
- Verify: jira: honors a configured tasks:jira_done_status override
   - Expected: code equals `0`
   - Expected: log contains `jira workitem transition PROJ-1 --status Resolved`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("jira: honors a configured tasks:jira_done_status override")
step("Verify: jira: honors a configured tasks:jira_done_status override")
reset_fixture()
clear_fixture_config()
write_fixture_config("", "Resolved", "", "", "")
install_fake_bin("acli", FAKE_ACLI_OK)
val (code, log) = run_tasks(["close", "PROJ-1", "--backend", "jira"])
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(log.contains("jira workitem transition PROJ-1 --status Resolved")).to_equal(true)
```

</details>

#### jira: --reason has no equivalent and is not forwarded to acli

- jira: --reason has no equivalent and is not forwarded to acli
- Verify: jira: --reason has no equivalent and is not forwarded to acli
   - Expected: code equals `0`
   - Expected: log does not contain `--reason`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("jira: --reason has no equivalent and is not forwarded to acli")
step("Verify: jira: --reason has no equivalent and is not forwarded to acli")
reset_fixture()
clear_fixture_config()
install_fake_bin("acli", FAKE_ACLI_OK)
val (code, log) = run_tasks(["close", "PROJ-1", "--backend", "jira", "--reason", "not planned"])
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(log.contains("--reason")).to_equal(false)
```

</details>

#### edit

#### github: G5 workaround calls gh directly for `issue edit`

- github: G5 workaround calls gh directly for `issue edit`
- Verify: github: G5 workaround calls gh directly for `issue edit`
   - Expected: code equals `0`
   - Expected: log contains `issue edit 123 --add-label bug`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("github: G5 workaround calls gh directly for `issue edit`")
step("Verify: github: G5 workaround calls gh directly for `issue edit`")
reset_fixture()
clear_fixture_config()
install_fake_bin("gh", FAKE_GH_OK)
val (code, log) = run_tasks(["edit", "123", "--backend", "github", "--add-label", "bug"])
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(log.contains("issue edit 123 --add-label bug")).to_equal(true)
```

</details>

#### jira: --title/--body translate to `update --summary/--description`

- jira: --title/--body translate to `update --summary/--description`
- Verify: jira: --title/--body translate to `update --summary/--description`
   - Expected: code equals `0`
   - Expected: log contains `jira workitem edit PROJ-1 --summary New T --description New B`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("jira: --title/--body translate to `update --summary/--description`")
step("Verify: jira: --title/--body translate to `update --summary/--description`")
reset_fixture()
clear_fixture_config()
install_fake_bin("acli", FAKE_ACLI_OK)
val (code, log) = run_tasks(["edit", "PROJ-1", "--backend", "jira", "--title", "New T", "--body", "New B"])
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(log.contains("jira workitem edit PROJ-1 --summary New T --description New B")).to_equal(true)
```

</details>

#### jira: --status transitions via `transition`

- jira: --status transitions via `transition`
- Verify: jira: --status transitions via `transition`
   - Expected: code equals `0`
   - Expected: log contains `jira workitem transition PROJ-1 --status In Progress`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("jira: --status transitions via `transition`")
step("Verify: jira: --status transitions via `transition`")
reset_fixture()
clear_fixture_config()
install_fake_bin("acli", FAKE_ACLI_OK)
val (code, log) = run_tasks(["edit", "PROJ-1", "--backend", "jira", "--status", "In Progress"])
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(log.contains("jira workitem transition PROJ-1 --status In Progress")).to_equal(true)
```

</details>

#### jira: --add-label is a defined not-yet-supported gap (G1b), exits 1

- jira: --add-label is a defined not-yet-supported gap (G1b), exits 1
- Verify: jira: --add-label is a defined not-yet-supported gap (G1b), exits 1
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("jira: --add-label is a defined not-yet-supported gap (G1b), exits 1")
step("Verify: jira: --add-label is a defined not-yet-supported gap (G1b), exits 1")
reset_fixture()
clear_fixture_config()
val (code, _log) = run_tasks(["edit", "PROJ-1", "--backend", "jira", "--add-label", "bug"])
expect(code).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### jira: no edit flags at all exits 1

- jira: no edit flags at all exits 1
- Verify: jira: no edit flags at all exits 1
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("jira: no edit flags at all exits 1")
step("Verify: jira: no edit flags at all exits 1")
reset_fixture()
clear_fixture_config()
val (code, _log) = run_tasks(["edit", "PROJ-1", "--backend", "jira"])
expect(code).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### errors

#### unknown top-level verb exits 1

- unknown top-level verb exits 1
- Verify: unknown top-level verb exits 1
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("unknown top-level verb exits 1")
step("Verify: unknown top-level verb exits 1")
reset_fixture()
clear_fixture_config()
val (code, _log) = run_tasks(["bogus"])
expect(code).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### invalid --backend value exits 1

- invalid --backend value exits 1
- Verify: invalid --backend value exits 1
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("invalid --backend value exits 1")
step("Verify: invalid --backend value exits 1")
reset_fixture()
clear_fixture_config()
val (code, _log) = run_tasks(["list", "--backend", "nope"])
expect(code).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### missing id for view exits 1

- missing id for view exits 1
- Verify: missing id for view exits 1
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("missing id for view exits 1")
step("Verify: missing id for view exits 1")
reset_fixture()
clear_fixture_config()
val (code, _log) = run_tasks(["view"])
expect(code).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 54 |
| Active scenarios | 54 |
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

- Canonical SPipe generation for source `3973ba7cedd479cd4bb7fed8509726858482a1bb7ace1b163e581ba3cb385a02`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3973ba7cedd479cd4bb7fed8509726858482a1bb7ace1b163e581ba3cb385a02`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3973ba7cedd479cd4bb7fed8509726858482a1bb7ace1b163e581ba3cb385a02`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/app/devhub/cmd_tasks_spec.spl
mirror: doc/06_spec/01_unit/app/devhub/cmd_tasks_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/devhub/cmd_tasks_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/devhub/cmd_tasks_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/devhub/cmd_tasks_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/devhub/cmd_tasks_spec.spl:144:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'golden case: @me assignee synthesizes currentUser(), default open state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/devhub/cmd_tasks_spec.spl:151:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a literal (non-@me) assignee becomes a quoted JQL literal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/devhub/cmd_tasks_spec.spl:157:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'label filter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
