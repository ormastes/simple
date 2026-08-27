# @manual: primary

> Purpose: Prove that UI SSR Hydration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Prove that UI SSR Hydration.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that UI SSR Hydration.
Audience: compiler and tooling engineers who maintain this spec.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines;
a failing scenario pinpoints the behavior that regressed.
## Compatibility and limitations
Covers the pinned behavior only; fixture data is local to this spec.
# @manual: primary
REQ-FEATURE-UI-SSR-001
doc/01_research/feature/REQ-FEATURE-UI-SSR-001.md
doc/03_plan/feature/REQ-FEATURE-UI-SSR-001.md
doc/04_architecture/feature/REQ-FEATURE-UI-SSR-001.md
doc/05_design/feature/REQ-FEATURE-UI-SSR-001.md

## Scenarios

### UI SSR Hydration

#### when rendering to string

#### round-trips server markup through parse and serialize

- Parse the SSR markup and serialize it back


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-FEATURE-UI-SSR-001
step("Parse the SSR markup and serialize it back")
val ssr = "<html><body><div id=\"root\"><p>hello</p></div></body></html>"
val dom = html_parse_text(ssr)
assert_equal(html_serialize(dom), ssr)
```

</details>

#### reports the tags the server markup contains

- Enumerate used_tags on the SSR fixture


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-FEATURE-UI-SSR-001
step("Enumerate used_tags on the SSR fixture")
val tags = used_tags("<html><body><div><p>x</p></div></body></html>")
assert_equal(tags.contains("div"), true)
assert_equal(tags.contains("p"), true)
assert_equal(tags.contains("span"), false)
```

</details>

#### when hydrating on client

#### hydrates an island by injecting a child without re-rendering siblings

- add_element a button island into the server div


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-FEATURE-UI-SSR-001
step("add_element a button island into the server div")
val ssr = "<html><body><div id=\"root\"><p>hello</p></div></body></html>"
val hydrated = add_element(ssr, "div", "button", "island-1", "Click")
assert_equal(hydrated.contains("<p>hello</p>"), true)
assert_equal(hydrated.contains("Click"), true)
# The server-rendered paragraph position is preserved verbatim.
assert_equal(hydrated.find("<p>hello</p>") < hydrated.find("Click"), true)
```

</details>

#### lists the hydrated elements including the injected island

- list_elements after hydration


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-FEATURE-UI-SSR-001
step("list_elements after hydration")
val hydrated = add_element(
    "<html><body><div><p>a</p></div></body></html>",
    "div", "button", "island-2", "Go")
val elements = list_elements(hydrated)
assert_equal(elements.contains("button id=island-2"), true)
assert_equal(elements.contains("p"), true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d593c80302f3f17bacc89a8093e774b727b1b44342c66ecd3ed01f51d6c6fee7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d593c80302f3f17bacc89a8093e774b727b1b44342c66ecd3ed01f51d6c6fee7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d593c80302f3f17bacc89a8093e774b727b1b44342c66ecd3ed01f51d6c6fee7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/feature/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl
mirror: doc/06_spec/03_system/feature/features/ui_ssr_hydration/ui_ssr_hydration_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=55 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/features/ui_ssr_hydration/ui_ssr_hydration_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/feature/features/ui_ssr_hydration/ui_ssr_hydration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/features/ui_ssr_hydration/ui_ssr_hydration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, traceability, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips server markup through parse and serialize' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports the tags the server markup contains' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hydrates an island by injecting a child without re-rendering siblings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
