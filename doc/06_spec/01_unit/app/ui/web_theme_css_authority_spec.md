# Web Theme Css Authority Specification

> Tests covering Simple Web theme CSS authority.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Theme Css Authority Specification

## Scenarios

### Simple Web theme CSS authority

#### resolves a compatibility alias to the content-addressed package CSS

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- resolves a compatibility alias to the content-addressed package CSS


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("resolves a compatibility alias to the content-addressed package CSS")
val fingerprint = theme_package_fingerprint("aetheric_dark")
val css = generate_css("glass_obsidian_dark")
expect(css).to_contain("Folder theme package")
expect(css).to_contain("theme=aetheric_dark")
expect(css).to_contain("fingerprint={fingerprint}")
expect(css).to_contain("--ui-accent: #adc6ff")
expect(css).to_contain("--app-background-image")
```

</details>

#### preserves package-owned widget overrides

- preserves package-owned widget overrides


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("preserves package-owned widget overrides")
val css = generate_css("glass_obsidian_dark")
expect(css).to_contain(".widget-panel.focused, .wm-window.focused")
expect(css).to_contain("0 0 40px var(--glass-accent)")
```

</details>

#### does not select the legacy glass CSS generator

- does not select the legacy glass CSS generator
   - Expected: source does not contain `generate_" + "glass_css`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("does not select the legacy glass CSS generator")
val source = file_read(HTML_SOURCE) + file_read(HTML_CSS_SOURCE)
expect(source.contains("generate_" + "glass_css")).to_equal(false)
```

</details>

#### accepts installed CSS only when its package fingerprint matches

- accepts installed CSS only when its package fingerprint matches
   - Expected: source does not contain `load_theme_package(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("accepts installed CSS only when its package fingerprint matches")
val source = file_read(HTML_SOURCE) + file_read(HTML_CSS_SOURCE)
expect(source).to_contain("active_theme_source_fingerprint")
expect(source).to_contain("resolved_theme_fingerprint")
expect(source).to_contain("installed_fingerprint == resolved_fingerprint")
expect(source).to_contain("resolved_theme_css")
expect(source.contains("load_theme_package(")).to_equal(false)
```

</details>

#### projects the selected package snapshot without carrying its aggregate into the browser frame

- projects the selected package snapshot without carrying its aggregate into the browser frame
   - Expected: source does not contain `load_theme_package(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("projects the selected package snapshot without carrying its aggregate into the browser frame")
val source = file_read(BROWSER_BACKEND_SOURCE)
expect(source).to_contain("theme_package_render_snapshot(state.tree.theme_name())")
expect(source.contains("load_theme_package(")).to_equal(false)
```

</details>

#### replaces only root attributes owned by the theme envelope

- replaces only root attributes owned by the theme envelope
   - Expected: source does not contain `startsWith('data-wm-')`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("replaces only root attributes owned by the theme envelope")
val source = file_read("src/app/ui.web/wm.js")
expect(source).to_contain("_applyThemeRootAttrs(rootAttrs)")
expect(source).to_contain("root.removeAttribute(attrName)")
expect(source).to_contain("Object.prototype.hasOwnProperty.call(entry, 'root_attrs')")
expect(source).to_contain("if (hasRootAttrs) envelope.root_attrs = root_attrs")
expect(source.contains("startsWith('data-wm-')")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/web_theme_css_authority_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Simple Web theme CSS authority.
- Simple Web theme CSS authority

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `43747b919e8aa98f0733926eaacaf0106c36d341114d3333056ce9105d397546`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `43747b919e8aa98f0733926eaacaf0106c36d341114d3333056ce9105d397546`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `43747b919e8aa98f0733926eaacaf0106c36d341114d3333056ce9105d397546`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/app/ui/web_theme_css_authority_spec.spl
mirror: doc/06_spec/01_unit/app/ui/web_theme_css_authority_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/app/ui/web_theme_css_authority_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/ui/web_theme_css_authority_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/ui/web_theme_css_authority_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/app/ui/web_theme_css_authority_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/ui/web_theme_css_authority_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves a compatibility alias to the content-addressed package CSS' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/ui/web_theme_css_authority_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves package-owned widget overrides' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/ui/web_theme_css_authority_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not select the legacy glass CSS generator' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
