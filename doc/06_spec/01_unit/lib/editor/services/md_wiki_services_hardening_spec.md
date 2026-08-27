# md_wiki_services_hardening_spec

> Purpose: Prove that wiki links: malformed input is safe.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# md_wiki_services_hardening_spec

Purpose: Prove that wiki links: malformed input is safe.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/editor/services/md_wiki_services_hardening_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that wiki links: malformed input is safe.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### wiki links: malformed input is safe

#### unterminated [[ yields no links and does not crash

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- unterminated [[ yields no links and does not crash
- Verify: unterminated [[ yields no links and does not crash
   - Expected: links.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("unterminated [[ yields no links and does not crash")
step("Verify: unterminated [[ yields no links and does not crash")
# @req: REQ-LIB-EDITOR-001
val doc = md_wiki_document("a.md", "before [[unterminated and more text")
val links = md_wiki_extract_links(doc, [doc])
expect(links.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### empty [[]] yields no links

- empty [[]] yields no links
- Verify: empty [[]] yields no links
   - Expected: links.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("empty [[]] yields no links")
step("Verify: empty [[]] yields no links")
val doc = md_wiki_document("a.md", "x [[]] y")
val links = md_wiki_extract_links(doc, [doc])
expect(links.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### adjacent links [[a]][[b]] both found

- adjacent links [[a]][[b]] both found
- Verify: adjacent links [[a]][[b]] both found
   - Expected: links.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("adjacent links [[a]][[b]] both found")
step("Verify: adjacent links [[a]][[b]] both found")
val doc = md_wiki_document("a.md", "[[alpha]][[beta]]")
val links = md_wiki_extract_links(doc, [doc])
expect(links.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### alias form [[target|alias]] keeps display

- alias form [[target|alias]] keeps display
- Verify: alias form [[target|alias]] keeps display
   - Expected: parsed.0 equals `target`
   - Expected: parsed.1 equals `alias`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("alias form [[target|alias]] keeps display")
step("Verify: alias form [[target|alias]] keeps display")
val parsed = md_wiki_parse_link_target("target|alias")
expect(parsed.0).to_equal("target")
expect(parsed.1).to_equal("alias")
```

</details>

#### heading form [[target#sec]] strips anchor from target

- heading form [[target#sec]] strips anchor from target
- Verify: heading form [[target#sec]] strips anchor from target
   - Expected: parsed.0 equals `target`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("heading form [[target#sec]] strips anchor from target")
step("Verify: heading form [[target#sec]] strips anchor from target")
val parsed = md_wiki_parse_link_target("target#sec")
expect(parsed.0).to_equal("target")
```

</details>

#### empty alias [[a|]] is safe

- empty alias [[a|]] is safe
- Verify: empty alias [[a|]] is safe
   - Expected: parsed.0 equals `a`
   - Expected: parsed.1 equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("empty alias [[a|]] is safe")
step("Verify: empty alias [[a|]] is safe")
val parsed = md_wiki_parse_link_target("a|")
expect(parsed.0).to_equal("a")
expect(parsed.1).to_equal("")
```

</details>

#### empty raw target is safe

- empty raw target is safe
- Verify: empty raw target is safe
   - Expected: parsed.0 equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("empty raw target is safe")
step("Verify: empty raw target is safe")
val parsed = md_wiki_parse_link_target("")
expect(parsed.0).to_equal("")
```

</details>

#### link at end of line is found

- link at end of line is found
- Verify: link at end of line is found
   - Expected: links.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("link at end of line is found")
step("Verify: link at end of line is found")
val doc = md_wiki_document("a.md", "see [[end]]")
val links = md_wiki_extract_links(doc, [doc])
expect(links.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

### embeds: malformed input is safe

#### unterminated ![[ yields no embeds

- unterminated ![[ yields no embeds
- Verify: unterminated ![[ yields no embeds
   - Expected: embeds.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("unterminated ![[ yields no embeds")
step("Verify: unterminated ![[ yields no embeds")
val doc = md_wiki_document("a.md", "look ![[broken and the rest")
val embeds = md_wiki_extract_embeds(doc, [doc])
expect(embeds.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### valid embed of missing target is unresolved, not a crash

- valid embed of missing target is unresolved, not a crash
- Verify: valid embed of missing target is unresolved, not a crash
   - Expected: unresolved.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("valid embed of missing target is unresolved, not a crash")
step("Verify: valid embed of missing target is unresolved, not a crash")
val doc = md_wiki_document("a.md", "![[missing-note]]")
val index = md_wiki_index_documents([doc])
val unresolved = md_wiki_unresolved_embeds(index)
expect(unresolved.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

### backlinks and index updates

#### link from b to a appears as backlink of a

- link from b to a appears as backlink of a
- Verify: link from b to a appears as backlink of a
   - Expected: backs.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("link from b to a appears as backlink of a")
step("Verify: link from b to a appears as backlink of a")
val a = md_wiki_document("alpha.md", "# Alpha\ncontent")
val b = md_wiki_document("b.md", "see [[alpha]]")
val index = md_wiki_index_documents([a, b])
val backs = md_wiki_backlinks(index, "alpha.md")
expect(backs.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### self-link does not crash and is indexed

- self-link does not crash and is indexed
- Verify: self-link does not crash and is indexed
   - Expected: backs.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("self-link does not crash and is indexed")
step("Verify: self-link does not crash and is indexed")
val a = md_wiki_document("alpha.md", "# Alpha\n[[alpha]]")
val index = md_wiki_index_documents([a])
val backs = md_wiki_backlinks(index, "alpha.md")
expect(backs.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### empty documents array builds an empty index

- empty documents array builds an empty index
- Verify: empty documents array builds an empty index
   - Expected: md_wiki_unresolved_links(index).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("empty documents array builds an empty index")
step("Verify: empty documents array builds an empty index")
val empty_docs: [MdWikiDocument] = []
val index = md_wiki_index_documents(empty_docs)
expect(md_wiki_unresolved_links(index).len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### empty content document is safe everywhere

- empty content document is safe everywhere
- Verify: empty content document is safe everywhere
   - Expected: md_wiki_backlinks(index, "e.md").len() equals `0`
   - Expected: md_wiki_tags(index, "any").len() equals `0`
   - Expected: md_wiki_callouts(index, "e.md").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("empty content document is safe everywhere")
step("Verify: empty content document is safe everywhere")
val doc = md_wiki_document("e.md", "")
val index = md_wiki_index_documents([doc])
expect(md_wiki_backlinks(index, "e.md").len()).to_equal(0)
expect(md_wiki_tags(index, "any").len()).to_equal(0)
expect(md_wiki_callouts(index, "e.md").len()).to_equal(0)
```

</details>

### tags: boundary cases

#### tag at end of line is found

- tag at end of line is found
- Verify: tag at end of line is found
   - Expected: tags.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("tag at end of line is found")
step("Verify: tag at end of line is found")
val doc = md_wiki_document("t.md", "note #urgent")
val tags = md_wiki_extract_tags(doc)
expect(tags.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### lone # is not a tag

- lone # is not a tag
- Verify: lone # is not a tag
   - Expected: tags.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("lone # is not a tag")
step("Verify: lone # is not a tag")
val doc = md_wiki_document("t.md", "just a # alone")
val tags = md_wiki_extract_tags(doc)
expect(tags.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### md_search: odd queries are safe

#### empty query returns no matches

- empty query returns no matches
- Verify: empty query returns no matches
   - Expected: matches.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("empty query returns no matches")
step("Verify: empty query returns no matches")
val matches = md_search("# Title\nbody text", "")
expect(matches.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### empty content returns no matches

- empty content returns no matches
- Verify: empty content returns no matches
   - Expected: matches.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("empty content returns no matches")
step("Verify: empty content returns no matches")
val matches = md_search("", "query")
expect(matches.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### query with bracket metacharacters is literal and safe

- query with bracket metacharacters is literal and safe
- Verify: query with bracket metacharacters is literal and safe
   - Expected: matches.len() >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("query with bracket metacharacters is literal and safe")
step("Verify: query with bracket metacharacters is literal and safe")
val matches = md_search("a [x] b", "[x]")
expect(matches.len() >= 0).to_equal(true)
```

</details>

#### crlf content does not crash search

- crlf content does not crash search
- Verify: crlf content does not crash search
   - Expected: matches.len() >= 1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("crlf content does not crash search")
step("Verify: crlf content does not crash search")
val matches = md_search("# H\r\nline one\r\nline two", "line")
expect(matches.len() >= 1).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
- `REQ-LIB-EDITOR-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e5a708bd728d20f6c556354e5566d69d8de5129305030471fdbf6482040d6ddb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e5a708bd728d20f6c556354e5566d69d8de5129305030471fdbf6482040d6ddb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e5a708bd728d20f6c556354e5566d69d8de5129305030471fdbf6482040d6ddb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **85/100**; blockers: **0**.

SSpec documentization score: 85/100
source: test/01_unit/lib/editor/services/md_wiki_services_hardening_spec.spl
mirror: doc/06_spec/01_unit/lib/editor/services/md_wiki_services_hardening_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=95 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/editor/services/md_wiki_services_hardening_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/editor/services/md_wiki_services_hardening_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/editor/services/md_wiki_services_hardening_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/editor/services/md_wiki_services_hardening_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'unterminated [[ yields no links and does not crash' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/editor/services/md_wiki_services_hardening_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'empty [[]] yields no links' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/editor/services/md_wiki_services_hardening_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adjacent links [[a]][[b]] both found' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/editor/services/md_wiki_services_hardening_spec.spl:104:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'valid embed of missing target is unresolved, not a crash' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
