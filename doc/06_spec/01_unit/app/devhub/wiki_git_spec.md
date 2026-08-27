# Wiki Git Specification

> Tests covering wiki_git sanitizers (mirrors app.portal.git_repo's sanitizer style), wiki_git against a local fixture wiki repo.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wiki Git Specification

## Scenarios

### wiki_git sanitizers (mirrors app.portal.git_repo's sanitizer style)

#### sanitize_wiki_page_name

#### accepts a normal page name

- accepts a normal page name
   - Expected: _rejects_page_name("Home") is false
   - Expected: _rejects_page_name("Getting-Started") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("accepts a normal page name")
expect(_rejects_page_name("Home")).to_equal(false)
expect(_rejects_page_name("Getting-Started")).to_equal(false)
```

</details>

#### rejects an empty page name

- rejects an empty page name
   - Expected: _rejects_page_name("") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects an empty page name")
expect(_rejects_page_name("")).to_equal(true)
```

</details>

#### rejects parent-directory traversal

- rejects parent-directory traversal
   - Expected: _rejects_page_name("../../etc/passwd") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects parent-directory traversal")
expect(_rejects_page_name("../../etc/passwd")).to_equal(true)
```

</details>

#### rejects a page name that looks like a git option

- rejects a page name that looks like a git option
   - Expected: _rejects_page_name("--upload-pack=/bin/sh") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects a page name that looks like a git option")
expect(_rejects_page_name("--upload-pack=/bin/sh")).to_equal(true)
```

</details>

#### rejects a page name with a path separator (flat namespace only)

- rejects a page name with a path separator (flat namespace only)
   - Expected: _rejects_page_name("a/b") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects a page name with a path separator (flat namespace only)")
expect(_rejects_page_name("a/b")).to_equal(true)
```

</details>

#### rejects a page name with shell metacharacters

- rejects a page name with shell metacharacters
   - Expected: _rejects_page_name("page; rm -rf /") is true
   - Expected: _rejects_page_name("page$(whoami)") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects a page name with shell metacharacters")
expect(_rejects_page_name("page; rm -rf /")).to_equal(true)
expect(_rejects_page_name("page$(whoami)")).to_equal(true)
```

</details>

#### rejects a leading dot

- rejects a leading dot
   - Expected: _rejects_page_name(".hidden") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects a leading dot")
expect(_rejects_page_name(".hidden")).to_equal(true)
```

</details>

#### sanitize_owner_or_repo

#### accepts a normal segment

- accepts a normal segment
   - Expected: _rejects_owner_or_repo("simple") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("accepts a normal segment")
expect(_rejects_owner_or_repo("simple")).to_equal(false)
```

</details>

#### rejects traversal, option-looking, and empty values

- rejects traversal, option-looking, and empty values
   - Expected: _rejects_owner_or_repo("..") is true
   - Expected: _rejects_owner_or_repo("-x") is true
   - Expected: _rejects_owner_or_repo("") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects traversal, option-looking, and empty values")
expect(_rejects_owner_or_repo("..")).to_equal(true)
expect(_rejects_owner_or_repo("-x")).to_equal(true)
expect(_rejects_owner_or_repo("")).to_equal(true)
```

</details>

#### sanitize_owner_repo_slug

#### splits and validates a valid owner/repo

- splits and validates a valid owner/repo
   - Expected: true is false
   - Expected: pair.0 equals `acme`
   - Expected: pair.1 equals `widgets`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("splits and validates a valid owner/repo")
match sanitize_owner_repo_slug("acme/widgets"):
    Err(_msg):
        expect(true).to_equal(false)
    Ok(pair):
        expect(pair.0).to_equal("acme")
        expect(pair.1).to_equal("widgets")
```

</details>

#### rejects a slug without exactly one slash

- rejects a slug without exactly one slash
   - Expected: true is true
   - Expected: true is false
   - Expected: true is true
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects a slug without exactly one slash")
match sanitize_owner_repo_slug("bogus"):
    Err(_msg):
        expect(true).to_equal(true)
    Ok(_pair):
        expect(true).to_equal(false)
match sanitize_owner_repo_slug("a/b/c"):
    Err(_msg):
        expect(true).to_equal(true)
    Ok(_pair):
        expect(true).to_equal(false)
```

</details>

### wiki_git against a local fixture wiki repo

#### clones a fresh cache dir

- clones a fresh cache dir
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("clones a fresh cache dir")
val bare_repo = _fixture_bare_wiki_repo()
val cache_dir = _fresh_temp_dir() + "/clone"
val (ok, _err) = wiki_git_clone_or_pull(bare_repo, cache_dir)
expect(ok).to_equal(true)
```

</details>

#### pulls without error on a second clone_or_pull against the same cache dir

- pulls without error on a second clone_or_pull against the same cache dir
   - Expected: ok1 is true
   - Expected: ok2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("pulls without error on a second clone_or_pull against the same cache dir")
val bare_repo = _fixture_bare_wiki_repo()
val cache_dir = _fresh_temp_dir() + "/clone"
val (ok1, _e1) = wiki_git_clone_or_pull(bare_repo, cache_dir)
expect(ok1).to_equal(true)
val (ok2, _e2) = wiki_git_clone_or_pull(bare_repo, cache_dir)
expect(ok2).to_equal(true)
```

</details>

#### lists the seeded pages

- lists the seeded pages
   - Expected: _list_contains(pages, "Home") is true
   - Expected: _list_contains(pages, "Setup") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("lists the seeded pages")
val bare_repo = _fixture_bare_wiki_repo()
val cache_dir = _fresh_temp_dir() + "/clone"
val (_ok, _err) = wiki_git_clone_or_pull(bare_repo, cache_dir)
val pages = wiki_git_list(cache_dir)
expect(_list_contains(pages, "Home")).to_equal(true)
expect(_list_contains(pages, "Setup")).to_equal(true)
```

</details>

#### reads an existing page's content

- reads an existing page's content
   - Expected: true is false
   - Expected: content contains `Welcome to the wiki`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reads an existing page's content")
val bare_repo = _fixture_bare_wiki_repo()
val cache_dir = _fresh_temp_dir() + "/clone"
val (_ok, _err) = wiki_git_clone_or_pull(bare_repo, cache_dir)
match wiki_git_read(cache_dir, "Home"):
    Err(_msg):
        expect(true).to_equal(false)
    Ok(content):
        expect(content.contains("Welcome to the wiki")).to_equal(true)
```

</details>

#### returns an error for a page that does not exist

- returns an error for a page that does not exist
   - Expected: true is true
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns an error for a page that does not exist")
val bare_repo = _fixture_bare_wiki_repo()
val cache_dir = _fresh_temp_dir() + "/clone"
val (_ok, _err) = wiki_git_clone_or_pull(bare_repo, cache_dir)
match wiki_git_read(cache_dir, "NoSuchPage"):
    Err(_msg):
        expect(true).to_equal(true)
    Ok(_content):
        expect(true).to_equal(false)
```

</details>

#### writes a new page and commits it locally, visible in a subsequent list

- writes a new page and commits it locally, visible in a subsequent list
   - Expected: write_ok is true
   - Expected: _list_contains(wiki_git_list(cache_dir), "NewPage") is true
   - Expected: true is false
   - Expected: content contains `Body.`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("writes a new page and commits it locally, visible in a subsequent list")
val bare_repo = _fixture_bare_wiki_repo()
val cache_dir = _fresh_temp_dir() + "/clone"
val (_ok, _err) = wiki_git_clone_or_pull(bare_repo, cache_dir)
val (write_ok, _write_err) = wiki_git_write(cache_dir, "NewPage", "# New Page\n\nBody.\n", "add NewPage")
expect(write_ok).to_equal(true)
expect(_list_contains(wiki_git_list(cache_dir), "NewPage")).to_equal(true)
match wiki_git_read(cache_dir, "NewPage"):
    Err(_msg):
        expect(true).to_equal(false)
    Ok(content):
        expect(content.contains("Body.")).to_equal(true)
```

</details>

#### rejects writing an invalid page name before touching the filesystem

- rejects writing an invalid page name before touching the filesystem
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects writing an invalid page name before touching the filesystem")
val cache_dir = _fresh_temp_dir()
val (ok, _err) = wiki_git_write(cache_dir, "../escape", "malicious", "")
expect(ok).to_equal(false)
```

</details>

#### deletes a page and commits the removal locally

- deletes a page and commits the removal locally
   - Expected: delete_ok is true
   - Expected: _list_contains(wiki_git_list(cache_dir), "Setup") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("deletes a page and commits the removal locally")
val bare_repo = _fixture_bare_wiki_repo()
val cache_dir = _fresh_temp_dir() + "/clone"
val (_ok, _err) = wiki_git_clone_or_pull(bare_repo, cache_dir)
val (delete_ok, _delete_err) = wiki_git_delete(cache_dir, "Setup", "remove Setup")
expect(delete_ok).to_equal(true)
expect(_list_contains(wiki_git_list(cache_dir), "Setup")).to_equal(false)
```

</details>

#### returns an error deleting a page that does not exist

- returns an error deleting a page that does not exist
   - Expected: delete_ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns an error deleting a page that does not exist")
val bare_repo = _fixture_bare_wiki_repo()
val cache_dir = _fresh_temp_dir() + "/clone"
val (_ok, _err) = wiki_git_clone_or_pull(bare_repo, cache_dir)
val (delete_ok, _delete_err) = wiki_git_delete(cache_dir, "NoSuchPage", "")
expect(delete_ok).to_equal(false)
```

</details>

#### searches for a term present in one page

- searches for a term present in one page
   - Expected: true is false
   - Expected: matches[0].page equals `Home`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("searches for a term present in one page")
val bare_repo = _fixture_bare_wiki_repo()
val cache_dir = _fresh_temp_dir() + "/clone"
val (_ok, _err) = wiki_git_clone_or_pull(bare_repo, cache_dir)
match wiki_git_search(cache_dir, "Welcome"):
    Err(_msg):
        expect(true).to_equal(false)
    Ok(matches):
        expect(matches.len()).to_be_greater_than(0)
        expect(matches[0].page).to_equal("Home")
```

</details>

#### search returns an empty (not error) result when no page matches

- search returns an empty (not error) result when no page matches
   - Expected: true is false
   - Expected: matches.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("search returns an empty (not error) result when no page matches")
val bare_repo = _fixture_bare_wiki_repo()
val cache_dir = _fresh_temp_dir() + "/clone"
val (_ok, _err) = wiki_git_clone_or_pull(bare_repo, cache_dir)
match wiki_git_search(cache_dir, "ThisTermDoesNotExistAnywhereAtAll"):
    Err(_msg):
        expect(true).to_equal(false)
    Ok(matches):
        expect(matches.len()).to_equal(0)
```

</details>

#### reports a non-empty last-modified string for a page with history

- reports a non-empty last-modified string for a page with history
   - Expected: wiki_git_page_modified(cache_dir, "Home") != "" is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reports a non-empty last-modified string for a page with history")
val bare_repo = _fixture_bare_wiki_repo()
val cache_dir = _fresh_temp_dir() + "/clone"
val (_ok, _err) = wiki_git_clone_or_pull(bare_repo, cache_dir)
expect(wiki_git_page_modified(cache_dir, "Home") != "").to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/devhub/wiki_git_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering wiki_git sanitizers (mirrors app.portal.git_repo's sanitizer style), wiki_git against a local fixture wiki repo.
- wiki_git sanitizers (mirrors app.portal.git_repo's sanitizer style)
- wiki_git against a local fixture wiki repo

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `eaf6788359d753807674eafe7dc0859d90c59ed7ff457e17bea2f731bb606037`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eaf6788359d753807674eafe7dc0859d90c59ed7ff457e17bea2f731bb606037`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eaf6788359d753807674eafe7dc0859d90c59ed7ff457e17bea2f731bb606037`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/app/devhub/wiki_git_spec.spl
mirror: doc/06_spec/01_unit/app/devhub/wiki_git_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/devhub/wiki_git_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/devhub/wiki_git_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/devhub/wiki_git_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/devhub/wiki_git_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a normal page name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/devhub/wiki_git_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an empty page name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/devhub/wiki_git_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects parent-directory traversal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
