# Cmd Github Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cmd Github Specification

## Scenarios

### itf github (fake-binary fixture)

#### issue list — success path

#### exits 0 and forwards the default --json fields to gh

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = install_fake_gh(FAKE_GH_LIST_OK)
val (code, log) = run_github_with_fake_gh(dir, ["issue", "list"])
expect(code).to_equal(0)
expect(log.contains("issue list --json number,title,state,author,updatedAt")).to_equal(true)
```

</details>

#### forwards extra gh-native flags (e.g. --state, --limit) verbatim

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = install_fake_gh(FAKE_GH_LIST_OK)
val (code, log) = run_github_with_fake_gh(dir, ["issue", "list", "--state", "open", "--limit", "5"])
expect(code).to_equal(0)
expect(log.contains("--state open --limit 5")).to_equal(true)
```

</details>

#### pr list — empty result

#### exits 0 on an empty array (no issues/PRs is not an error)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = install_fake_gh(FAKE_GH_LIST_OK)
val (code, _log) = run_github_with_fake_gh(dir, ["pr", "list"])
expect(code).to_equal(0)
```

</details>

#### gh missing

#### exits 1 with an actionable 'not found' error (never a bare crash)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = install_fake_gh(FAKE_GH_NOT_FOUND)
val (code, _log) = run_github_with_fake_gh(dir, ["issue", "list"])
expect(code).to_equal(1)
```

</details>

#### gh unauthenticated

#### exits 1 and does not fall through to a bare exit code

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = install_fake_gh(FAKE_GH_UNAUTHED)
val (code, log) = run_github_with_fake_gh(dir, ["issue", "list"])
expect(code).to_equal(1)
expect(log.contains("issue list")).to_equal(true)
```

</details>

#### unknown subcommand

#### exits 1 for an unknown top-level command without touching gh

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(handle_github(["bogus"])).to_equal(1)
```

</details>

#### exits 1 for an unknown issue subcommand

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(handle_github(["issue", "bogus"])).to_equal(1)
```

</details>

### cmd_github pure JSON-extraction helpers

#### _gh_field

#### extracts a string field, stripping quotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = json_parse("{\"title\":\"hello\"}")
expect(_gh_field(obj, "title")).to_equal("hello")
```

</details>

#### extracts a numeric field as text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = json_parse("{\"number\":42}")
expect(_gh_field(obj, "number")).to_equal("42")
```

</details>

#### returns empty text for a missing field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = json_parse("{\"title\":\"hello\"}")
expect(_gh_field(obj, "missing")).to_equal("")
```

</details>

#### _gh_login

#### extracts the nested login field gh uses for author/assignee

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = json_parse("{}")
expect(_gh_login(obj, "author")).to_equal("")
```

</details>

#### _default_fields

#### uses the pr field set (includes headRefName) for entity=pr

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_default_fields("pr")).to_equal("number,title,state,author,headRefName,updatedAt")
```

</details>

#### uses the issue field set for entity=issue

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_default_fields("issue")).to_equal("number,title,state,author,updatedAt")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/itf/cmd_github_spec.spl` |
| Updated | 2026-07-19 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- itf github (fake-binary fixture)
- cmd_github pure JSON-extraction helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
