# wiki_backend_routing_spec

> Purpose: Prove that devhub wiki --backend routing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# wiki_backend_routing_spec

Purpose: Prove that devhub wiki --backend routing.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/devhub/wiki_backend_routing_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that devhub wiki --backend routing.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### devhub wiki --backend routing

#### confluence (default, untouched)

#### routes the default (no --backend) identically to explicit --backend confluence

- routes the default (no --backend) identically to explicit --backend confluence
- Verify: routes the default (no --backend) identically to explicit --backend confluence
   - Expected: code_default equals `code_explicit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("routes the default (no --backend) identically to explicit --backend confluence")
step("Verify: routes the default (no --backend) identically to explicit --backend confluence")
# @req: REQ-APP-DEVHUB-001
# Pinned to FIXTURE_HOME with no wiki config so this holds
# deterministically even on a machine whose real ~/.config/itf
# sets `wiki: default_backend: github` (see header comment).
_clear_wiki_config()
val code_default = _run_wiki_with_home(["list"])
val code_explicit = _run_wiki_with_home(["list", "--backend", "confluence"])
expect(code_default).to_equal(code_explicit)
```

</details>

#### unknown --backend

#### exits 1 with an actionable error, without attempting any clone

- exits 1 with an actionable error, without attempting any clone
- Verify: exits 1 with an actionable error, without attempting any clone
   - Expected: handle_wiki(["list", "--backend", "bogus"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("exits 1 with an actionable error, without attempting any clone")
step("Verify: exits 1 with an actionable error, without attempting any clone")
expect(handle_wiki(["list", "--backend", "bogus"])).to_equal(1)
```

</details>

#### github — missing --repo

#### exits 1 without attempting a clone

- exits 1 without attempting a clone
- Verify: exits 1 without attempting a clone
   - Expected: handle_wiki(["list", "--backend", "github"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("exits 1 without attempting a clone")
step("Verify: exits 1 without attempting a clone")
expect(handle_wiki(["list", "--backend", "github"])).to_equal(1)
```

</details>

#### github — invalid --repo shape

#### exits 1 for a slug that is not owner/repo

- exits 1 for a slug that is not owner/repo
- Verify: exits 1 for a slug that is not owner/repo
   - Expected: handle_wiki(["list", "--backend", "github", "--repo", "bogus"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("exits 1 for a slug that is not owner/repo")
step("Verify: exits 1 for a slug that is not owner/repo")
expect(handle_wiki(["list", "--backend", "github", "--repo", "bogus"])).to_equal(1)
```

</details>

#### github — delete confirmation gate

#### exits 2 without --yes, before any clone is attempted

- exits 2 without --yes, before any clone is attempted
- Verify: exits 2 without --yes, before any clone is attempted
   - Expected: handle_wiki(["delete", "Home", "--backend", "github", "--repo", "acme/demo"]) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("exits 2 without --yes, before any clone is attempted")
step("Verify: exits 2 without --yes, before any clone is attempted")
expect(handle_wiki(["delete", "Home", "--backend", "github", "--repo", "acme/demo"])).to_equal(2)
```

</details>

#### github — end to end against a local fixture wiki repo

#### list exits 0 and syncs the fixture

- list exits 0 and syncs the fixture
- Verify: list exits 0 and syncs the fixture
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("list exits 0 and syncs the fixture")
step("Verify: list exits 0 and syncs the fixture")
val bare_repo = _fixture_bare_wiki_repo()
val cache_root = _fresh_temp_dir()
val code = _run_wiki_github(bare_repo, cache_root, ["list", "--backend", "github", "--repo", "acme/demo"])
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### view exits 0 for the seeded page and 1 for a missing one

- view exits 0 for the seeded page and 1 for a missing one
- Verify: view exits 0 for the seeded page and 1 for a missing one
   - Expected: code_ok equals `0`
   - Expected: code_missing equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("view exits 0 for the seeded page and 1 for a missing one")
step("Verify: view exits 0 for the seeded page and 1 for a missing one")
val bare_repo = _fixture_bare_wiki_repo()
val cache_root = _fresh_temp_dir()
val code_ok = _run_wiki_github(bare_repo, cache_root, ["view", "Home", "--backend", "github", "--repo", "acme/demo"])
expect(code_ok).to_equal(0)  # oracle: 0 — named expected value from the requirement
val code_missing = _run_wiki_github(bare_repo, cache_root, ["view", "NoSuchPage", "--backend", "github", "--repo", "acme/demo"])
expect(code_missing).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### search exits 0 for a matching term

- search exits 0 for a matching term
- Verify: search exits 0 for a matching term
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("search exits 0 for a matching term")
step("Verify: search exits 0 for a matching term")
val bare_repo = _fixture_bare_wiki_repo()
val cache_root = _fresh_temp_dir()
val code = _run_wiki_github(bare_repo, cache_root, ["search", "Welcome", "--backend", "github", "--repo", "acme/demo"])
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### create commits locally without --push, and delete --yes removes it locally

- create commits locally without --push, and delete --yes removes it locally
- Verify: create commits locally without --push, and delete --yes removes it locally
   - Expected: create_code equals `0`
   - Expected: view_code equals `0`
   - Expected: delete_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("create commits locally without --push, and delete --yes removes it locally")
step("Verify: create commits locally without --push, and delete --yes removes it locally")
val bare_repo = _fixture_bare_wiki_repo()
val cache_root = _fresh_temp_dir()
val create_code = _run_wiki_github(bare_repo, cache_root, ["create", "--backend", "github", "--repo", "acme/demo", "--title", "NewPage"])
expect(create_code).to_equal(0)  # oracle: 0 — named expected value from the requirement

val view_code = _run_wiki_github(bare_repo, cache_root, ["view", "NewPage", "--backend", "github", "--repo", "acme/demo"])
expect(view_code).to_equal(0)  # oracle: 0 — named expected value from the requirement

val delete_code = _run_wiki_github(bare_repo, cache_root, ["delete", "NewPage", "--backend", "github", "--repo", "acme/demo", "--yes"])
expect(delete_code).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### never pushes: a page created without --push is invisible from a fresh clone of the fixture remote

- never pushes: a page created without --push is invisible from a fresh clone of the fixture remote
- Verify: never pushes: a page created without --push is invisible from a fresh clone of the fixture remote
   - Expected: create_code equals `0`
   - Expected: verify_code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("never pushes: a page created without --push is invisible from a fresh clone of the fixture remote")
step("Verify: never pushes: a page created without --push is invisible from a fresh clone of the fixture remote")
val bare_repo = _fixture_bare_wiki_repo()
val cache_root_a = _fresh_temp_dir()
val create_code = _run_wiki_github(bare_repo, cache_root_a, ["create", "--backend", "github", "--repo", "acme/demo", "--title", "NeverPushed"])
expect(create_code).to_equal(0)  # oracle: 0 — named expected value from the requirement

# A second, independent cache root forces a brand-new clone
# straight from the fixture remote — if NeverPushed leaked
# through a push, it would show up here too.
val cache_root_b = _fresh_temp_dir()
val verify_code = _run_wiki_github(bare_repo, cache_root_b, ["view", "NeverPushed", "--backend", "github", "--repo", "acme/demo"])
expect(verify_code).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

### devhub wiki wiki.default_backend config (D1 precedence step 2, gap G6)

#### no wiki config at all

#### falls back to confluence — pre-existing default, verbatim (exit 4: no confluence auth in the fixture HOME)

- falls back to confluence — pre-existing default, verbatim (exit 4: no confluence auth in the fixture HOME)
- Verify: falls back to confluence — pre-existing default, verbatim (exit 4: no confluence auth in the fixture HOME)
   - Expected: code equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("falls back to confluence — pre-existing default, verbatim (exit 4: no confluence auth in the fixture HOME)")
step("Verify: falls back to confluence — pre-existing default, verbatim (exit 4: no confluence auth in the fixture HOME)")
_clear_wiki_config()
val code = _run_wiki_with_home(["list"])
expect(code).to_equal(4)  # oracle: 4 — named expected value from the requirement
```

</details>

#### default_backend: github, no --backend flag

#### routes to github from config alone (missing --repo -> exit 1, not confluence's auth-required exit 4)

- routes to github from config alone (missing --repo -> exit 1, not confluence's auth-required exit 4)
- Verify: routes to github from config alone (missing --repo -> exit 1, not confluence's auth-required exit 4)
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("routes to github from config alone (missing --repo -> exit 1, not confluence's auth-required exit 4)")
step("Verify: routes to github from config alone (missing --repo -> exit 1, not confluence's auth-required exit 4)")
_write_wiki_config("github")
val code = _run_wiki_with_home(["list"])
_clear_wiki_config()
expect(code).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### end to end against a local fixture wiki repo: list exits 0 via config default alone

- end to end against a local fixture wiki repo: list exits 0 via config default alone
- Verify: end to end against a local fixture wiki repo: list exits 0 via config default alone
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("end to end against a local fixture wiki repo: list exits 0 via config default alone")
step("Verify: end to end against a local fixture wiki repo: list exits 0 via config default alone")
_write_wiki_config("github")
val bare_repo = _fixture_bare_wiki_repo()
val cache_root = _fresh_temp_dir()
val code = _run_wiki_github_with_home(bare_repo, cache_root, ["list", "--repo", "acme/demo"])
_clear_wiki_config()
expect(code).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### default_backend: github, explicit --backend confluence

#### explicit flag still wins over the configured default (D1) -> confluence's auth-required exit 4

- explicit flag still wins over the configured default (D1) -> confluence's auth-required exit 4
- Verify: explicit flag still wins over the configured default (D1) -> confluence's auth-required exit 4
   - Expected: code equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("explicit flag still wins over the configured default (D1) -> confluence's auth-required exit 4")
step("Verify: explicit flag still wins over the configured default (D1) -> confluence's auth-required exit 4")
_write_wiki_config("github")
val code = _run_wiki_with_home(["list", "--backend", "confluence"])
_clear_wiki_config()
expect(code).to_equal(4)  # oracle: 4 — named expected value from the requirement
```

</details>

#### default_backend: bogus

#### an invalid configured value is still routed to _wiki_unknown_backend -> exit 1

- an invalid configured value is still routed to _wiki_unknown_backend -> exit 1
- Verify: an invalid configured value is still routed to _wiki_unknown_backend -> exit 1
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("an invalid configured value is still routed to _wiki_unknown_backend -> exit 1")
step("Verify: an invalid configured value is still routed to _wiki_unknown_backend -> exit 1")
_write_wiki_config("bogus")
val code = _run_wiki_with_home(["list"])
_clear_wiki_config()
expect(code).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

### _wiki_edit_write_temp / _wiki_edit_read_temp (real file I/O, bug wiki-confluence-mock-file-io)

#### writes then reads back real content from a temp path

- writes then reads back real content from a temp path
- Verify: writes then reads back real content from a temp path
   - Expected: read_ok is true
   - Expected: read_back equals `content`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("writes then reads back real content from a temp path")
step("Verify: writes then reads back real content from a temp path")
val dir = _fresh_temp_dir()
val tmp_path = "{dir}/itf_wiki_edit_roundtrip.html"
val content = "<p>Hello from the wiki edit round-trip spec.</p>"
val _write_ok = _wiki_edit_write_temp(tmp_path, content)
val (read_ok, read_back) = _wiki_edit_read_temp(tmp_path)
expect(read_ok).to_equal(true)
expect(read_back).to_equal(content)
```

</details>

#### reports not-ok for a path that was never written

- reports not-ok for a path that was never written
- Verify: reports not-ok for a path that was never written
   - Expected: read_ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reports not-ok for a path that was never written")
step("Verify: reports not-ok for a path that was never written")
val dir = _fresh_temp_dir()
val missing_path = "{dir}/never-written.html"
val (read_ok, _read_back) = _wiki_edit_read_temp(missing_path)
expect(read_ok).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
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

- Canonical SPipe generation for source `544d89601308fd268469021ba378b789556e4535f9f80d9a92fe3a54340f2f68`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `544d89601308fd268469021ba378b789556e4535f9f80d9a92fe3a54340f2f68`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `544d89601308fd268469021ba378b789556e4535f9f80d9a92fe3a54340f2f68`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/app/devhub/wiki_backend_routing_spec.spl
mirror: doc/06_spec/01_unit/app/devhub/wiki_backend_routing_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/devhub/wiki_backend_routing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/devhub/wiki_backend_routing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/devhub/wiki_backend_routing_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/devhub/wiki_backend_routing_spec.spl:158:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes the default (no --backend) identically to explicit --backend confluence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/devhub/wiki_backend_routing_spec.spl:173:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exits 1 with an actionable error, without attempting any clone' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/devhub/wiki_backend_routing_spec.spl:181:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exits 1 without attempting a clone' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
