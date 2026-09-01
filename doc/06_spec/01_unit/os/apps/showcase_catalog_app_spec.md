# Showcase Catalog App Specification

> Tests covering Showcase Catalog app.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Showcase Catalog App Specification

## Scenarios

### Showcase Catalog app

#### builds exactly the three canonical app panels with semantic identity fields

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds exactly the three canonical app panels with semantic identity fields
   - Expected: tree.title_text() equals `Showcase Catalog`
   - Expected: entries.len() equals `3`
   - Expected: tree.root_node().child_count() equals `3`
   - Expected: card.get_prop("title") equals `entry.title`
   - Expected: require_node(tree, "showcase_title_{entry.app_id}").get_prop("content") equals `entry.title`
   - Expected: require_node(tree, "showcase_app_id_{entry.app_id}").get_prop("content") equals `App ID: {entry.app_id}`
   - Expected: require_node(tree, "showcase_installed_path_{entry.app_id}").get_prop("content") equals `Installed path: {entry.installed_path}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("builds exactly the three canonical app panels with semantic identity fields")
val session = ShowcaseCatalogApp.new().build_ui()
val tree = session.current_tree()
expect(tree.title_text()).to_equal("Showcase Catalog")
val entries = showcase_catalog()
expect(entries.len()).to_equal(3)
expect(tree.root_node().child_count()).to_equal(3)
for entry in entries:
    val card = require_node(tree, "showcase_entry_{entry.app_id}")
    expect(card.get_prop("title")).to_equal(entry.title)
    expect(require_node(tree, "showcase_title_{entry.app_id}").get_prop("content")).to_equal(entry.title)
    expect(require_node(tree, "showcase_app_id_{entry.app_id}").get_prop("content")).to_equal("App ID: {entry.app_id}")
    expect(require_node(tree, "showcase_installed_path_{entry.app_id}").get_prop("content")).to_equal("Installed path: {entry.installed_path}")
```

</details>

#### derives honest readiness labels actions and disabled state from the shared catalog

- derives honest readiness labels actions and disabled state from the shared catalog


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("derives honest readiness labels actions and disabled state from the shared catalog")
val tree = ShowcaseCatalogApp.new().build_ui().current_tree()
for entry in showcase_catalog():
    verify_surface(tree, entry, ShowcaseSurface.Standalone, "standalone", "Standalone")
    verify_surface(tree, entry, ShowcaseSurface.HostWm, "host_wm", "Host WM")
    verify_surface(tree, entry, ShowcaseSurface.SimpleOsWm, "simpleos_wm", "SimpleOS WM")
    verify_surface(tree, entry, ShowcaseSurface.SimpleOs2d, "simpleos_2d", "SimpleOS 2D")
    verify_surface(tree, entry, ShowcaseSurface.SimpleOsWeb, "simpleos_web", "SimpleOS Web")
    verify_surface(tree, entry, ShowcaseSurface.SimpleOsGui, "simpleos_gui", "SimpleOS GUI")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/showcase_catalog_app_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Showcase Catalog app.
- Showcase Catalog app

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `421d0cb59e443f66ae2150721e8f670d8f4269dcd10bd6a54f63ddb690bdb9ee`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `421d0cb59e443f66ae2150721e8f670d8f4269dcd10bd6a54f63ddb690bdb9ee`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `421d0cb59e443f66ae2150721e8f670d8f4269dcd10bd6a54f63ddb690bdb9ee`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/os/apps/showcase_catalog_app_spec.spl
mirror: doc/06_spec/01_unit/os/apps/showcase_catalog_app_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/apps/showcase_catalog_app_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/apps/showcase_catalog_app_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/apps/showcase_catalog_app_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/apps/showcase_catalog_app_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds exactly the three canonical app panels with semantic identity fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/showcase_catalog_app_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'derives honest readiness labels actions and disabled state from the shared catalog' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
