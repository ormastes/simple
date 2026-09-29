# Portal Server Specification

> Tests covering portal server.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Portal Server Specification

## Scenarios

### portal server

#### serves the home page through the shared layout

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- serves the home page through the shared layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("serves the home page through the shared layout")
val resp = _server().route_request("GET", "/", "", "")
expect(resp).to_start_with("HTTP/1.1 200 OK")
expect(resp).to_contain("Simple Portal")
expect(resp).to_contain("Content-Security-Policy:")
```

</details>

#### serves the app stylesheet

- serves the app stylesheet


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("serves the app stylesheet")
val resp = _server().route_request("GET", "/css/app.css", "", "")
expect(resp).to_start_with("HTTP/1.1 200 OK")
expect(resp).to_contain("Content-Type: text/css")
```

</details>

#### lists the fixture repository

- lists the fixture repository


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("lists the fixture repository")
val resp = _server().route_request("GET", "/repos", "", "")
expect(resp).to_start_with("HTTP/1.1 200 OK")
expect(resp).to_contain("/repos/demo")
```

</details>

#### renders the repo landing page with the README

- renders the repo landing page with the README


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("renders the repo landing page with the README")
val resp = _server().route_request("GET", "/repos/demo", "", "")
expect(resp).to_start_with("HTTP/1.1 200 OK")
expect(resp).to_contain("Demo Repo")
```

</details>

#### lists the tree at the default ref

- lists the tree at the default ref


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("lists the tree at the default ref")
val resp = _server().route_request("GET", "/repos/demo/tree/main", "", "")
expect(resp).to_start_with("HTTP/1.1 200 OK")
expect(resp).to_contain("src")
expect(resp).to_contain("README.md")
```

</details>

#### lists a nested directory

- lists a nested directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("lists a nested directory")
val resp = _server().route_request("GET", "/repos/demo/tree/main/src", "", "")
expect(resp).to_start_with("HTTP/1.1 200 OK")
expect(resp).to_contain("main.spl")
```

</details>

#### shows a blob's content with the latest revision

- shows a blob's content with the latest revision


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("shows a blob's content with the latest revision")
val resp = _server().route_request("GET", "/repos/demo/blob/main/src/main.spl", "", "")
expect(resp).to_start_with("HTTP/1.1 200 OK")
expect(resp).to_contain("print 2")
```

</details>

#### lists commit history newest first

- lists commit history newest first


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("lists commit history newest first")
val resp = _server().route_request("GET", "/repos/demo/commits/main", "", "")
expect(resp).to_start_with("HTTP/1.1 200 OK")
expect(resp).to_contain("second commit")
expect(resp).to_contain("first commit")
```

</details>

#### renders a commit diff

- renders a commit diff


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("renders a commit diff")
val resp = _server().route_request("GET", "/repos/demo/commits/main", "", "")
expect(resp).to_contain("commit/")
```

</details>

#### returns a styled 404 for an unknown repository

- returns a styled 404 for an unknown repository


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns a styled 404 for an unknown repository")
val resp = _server().route_request("GET", "/repos/does-not-exist", "", "")
expect(resp).to_start_with("HTTP/1.1 404 Not Found")
expect(resp).to_contain("Back to home")
```

</details>

#### returns a styled 404 for an unknown top-level page

- returns a styled 404 for an unknown top-level page


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns a styled 404 for an unknown top-level page")
val resp = _server().route_request("GET", "/nope", "", "")
expect(resp).to_start_with("HTTP/1.1 404 Not Found")
```

</details>

#### rejects a repository name attempting path traversal

- rejects a repository name attempting path traversal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects a repository name attempting path traversal")
val resp = _server().route_request("GET", "/repos/../../etc", "", "")
expect(resp).to_start_with("HTTP/1.1 400 Bad Request")
```

</details>

#### rejects a path-traversal attempt inside a tree route

- rejects a path-traversal attempt inside a tree route


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects a path-traversal attempt inside a tree route")
val resp = _server().route_request("GET", "/repos/demo/tree/main/../../../etc", "", "")
expect(resp).to_start_with("HTTP/1.1 400 Bad Request")
```

</details>

#### rejects unsupported HTTP methods

- rejects unsupported HTTP methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects unsupported HTTP methods")
val resp = _server().route_request("POST", "/repos", "", "")
expect(resp).to_start_with("HTTP/1.1 405 Method Not Allowed")
```

</details>

#### resolves a branch ref containing a slash for the tree view

- resolves a branch ref containing a slash for the tree view


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("resolves a branch ref containing a slash for the tree view")
val resp = _server().route_request("GET", "/repos/demo/tree/feature/x", "", "")
expect(resp).to_start_with("HTTP/1.1 200 OK")
expect(resp).to_contain("href=\"/repos/demo/tree/feature/x/src\"")
```

</details>

#### resolves a blob under a branch ref containing a slash

- resolves a blob under a branch ref containing a slash


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("resolves a blob under a branch ref containing a slash")
val resp = _server().route_request("GET", "/repos/demo/blob/feature/x/src/feature.spl", "", "")
expect(resp).to_start_with("HTTP/1.1 200 OK")
expect(resp).to_contain("print 3")
```

</details>

#### resolves commits for a branch ref containing a slash

- resolves commits for a branch ref containing a slash


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("resolves commits for a branch ref containing a slash")
val resp = _server().route_request("GET", "/repos/demo/commits/feature/x", "", "")
expect(resp).to_start_with("HTTP/1.1 200 OK")
expect(resp).to_contain("feature branch commit")
```

</details>

#### does not double-list the repo when PORTAL_REPO_ROOT points directly at it

- does not double-list the repo when PORTAL_REPO_ROOT points directly at it
   - Expected: resp does not contain `href="/repos/"`
   - Expected: repo_link_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("does not double-list the repo when PORTAL_REPO_ROOT points directly at it")
val repo_root = _fixture_repo_root_is_itself_a_repo()
val server = PortalServer.with_repo_root("127.0.0.1", "0", repo_root)
val resp = server.route_request("GET", "/repos", "", "")
expect(resp).to_start_with("HTTP/1.1 200 OK")
expect(resp.contains("href=\"/repos/\"")).to_equal(false)
val repo_link_count = resp.split("<a href=\"/repos/").len() - 1
expect(repo_link_count).to_equal(1)
```

</details>

#### renders a submodule tree entry as non-link text instead of a 404 link

- renders a submodule tree entry as non-link text instead of a 404 link
   - Expected: resp does not contain `href="/repos/demo/tree/main/vendor"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("renders a submodule tree entry as non-link text instead of a 404 link")
val resp = _server().route_request("GET", "/repos/demo/tree/main", "", "")
expect(resp).to_start_with("HTTP/1.1 200 OK")
expect(resp).to_contain("submodule")
expect(resp).to_contain("vendor")
expect(resp.contains("href=\"/repos/demo/tree/main/vendor\"")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/portal/portal_server_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering portal server.
- portal server

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `146f80d053edfac89d359c2082a3e5c2a1eff9a29ea592c946e964e28d2e37e7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `146f80d053edfac89d359c2082a3e5c2a1eff9a29ea592c946e964e28d2e37e7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `146f80d053edfac89d359c2082a3e5c2a1eff9a29ea592c946e964e28d2e37e7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/02_integration/app/portal/portal_server_spec.spl
mirror: doc/06_spec/02_integration/app/portal/portal_server_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/portal/portal_server_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/portal/portal_server_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/portal/portal_server_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/app/portal/portal_server_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'serves the home page through the shared layout' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/portal/portal_server_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'serves the app stylesheet' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/portal/portal_server_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lists the fixture repository' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
