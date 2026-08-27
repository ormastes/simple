# md_wysiwyg_spec

> Markdown WYSIWYG view spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# md_wysiwyg_spec

Markdown WYSIWYG view spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/md_wysiwyg_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Markdown WYSIWYG view spec.

Verifies the "md tool: WYSIWYG beside line-by-line edit" slice — a side-by-side
view-model pairing each editable markdown source line with its rendered styled
preview, plus per-line edit-and-re-render. Pure model→view transform over the
shared office style resolver, so the IDE TUI and GUI can both consume it.

## Scenarios

### markdown WYSIWYG view: source and preview panes

#### has one row per source line

- has one row per source line
   - Expected: wysiwyg_line_count(view) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("has one row per source line")
val view = build_wysiwyg_view("alpha\nbeta\ngamma")
expect(wysiwyg_line_count(view)).to_equal(3)
```

</details>

#### preserves the source in the source pane

- preserves the source in the source pane
   - Expected: pane equals `alpha\nbeta`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("preserves the source in the source pane")
val view = build_wysiwyg_view("alpha\nbeta")
val pane = wysiwyg_source_pane(view)
expect(pane).to_equal("alpha\nbeta")
```

</details>

#### renders styled HTML in the preview pane

- renders styled HTML in the preview pane


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("renders styled HTML in the preview pane")
val view = build_wysiwyg_view("hello")
val pane = wysiwyg_preview_pane(view)
expect(pane).to_start_with("<div class=\"wysiwyg-preview\">")
expect(pane).to_contain("line-height: 1.5;")
expect(pane).to_contain(">hello</p>")
```

</details>

### markdown WYSIWYG view: beside-the-line editing
_Editing one line updates only that row's source and preview._

#### edits a single line's source

- edits a single line's source
   - Expected: pane equals `first\nchanged`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("edits a single line's source")
val view = build_wysiwyg_view("first\nsecond")
val edited = wysiwyg_update_line(view, 1, "changed")
val pane = wysiwyg_source_pane(edited)
expect(pane).to_equal("first\nchanged")
```

</details>

#### re-renders only the edited line's preview

- re-renders only the edited line's preview


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("re-renders only the edited line's preview")
val view = build_wysiwyg_view("first\nsecond")
val edited = wysiwyg_update_line(view, 1, "changed")
val preview = wysiwyg_preview_pane(edited)
expect(preview).to_contain(">first</p>")
expect(preview).to_contain(">changed</p>")
```

</details>

#### accepts checked edits only when expected source matches actual source

- accepts checked edits only when expected source matches actual source
   - Expected: result.reason equals `updated`
   - Expected: result.diff equals `@@ line 1 @@\n- second\n+ changed`
   - Expected: wysiwyg_source_pane(result.view) equals `first\nchanged`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("accepts checked edits only when expected source matches actual source")
val view = build_wysiwyg_view("first\nsecond")
val result = wysiwyg_update_line_checked(view, 1, "second", "changed")
expect(result.accepted).to_be(true)
expect(result.reason).to_equal("updated")
expect(result.diff).to_equal("@@ line 1 @@\n- second\n+ changed")
expect(wysiwyg_source_pane(result.view)).to_equal("first\nchanged")
```

</details>

#### rejects stale checked edits with expected and actual source

- rejects stale checked edits with expected and actual source
   - Expected: result.reason equals `stale-line`
   - Expected: result.actual_source equals `actual`
   - Expected: result.diff equals `@@ line 1 @@\nexpected: expected\nactual: actual\nrejected: changed`
   - Expected: wysiwyg_source_pane(result.view) equals `first\nactual`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects stale checked edits with expected and actual source")
val view = build_wysiwyg_view("first\nactual")
val result = wysiwyg_update_line_checked(view, 1, "expected", "changed")
expect(result.accepted).to_be(false)
expect(result.reason).to_equal("stale-line")
expect(result.actual_source).to_equal("actual")
expect(result.diff).to_equal("@@ line 1 @@\nexpected: expected\nactual: actual\nrejected: changed")
expect(wysiwyg_source_pane(result.view)).to_equal("first\nactual")
```

</details>

#### rejects checked edits for missing lines

- rejects checked edits for missing lines
   - Expected: result.reason equals `line-not-found`
   - Expected: result.actual_source equals `<missing>`
   - Expected: wysiwyg_source_pane(result.view) equals `first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects checked edits for missing lines")
val view = build_wysiwyg_view("first")
val result = wysiwyg_update_line_checked(view, 3, "expected", "changed")
expect(result.accepted).to_be(false)
expect(result.reason).to_equal("line-not-found")
expect(result.actual_source).to_equal("<missing>")
expect(wysiwyg_source_pane(result.view)).to_equal("first")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `38a5233b30b4c20ac8af20d71a2b6c0a4e266fcee3530addbc911901b54275fd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `38a5233b30b4c20ac8af20d71a2b6c0a4e266fcee3530addbc911901b54275fd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `38a5233b30b4c20ac8af20d71a2b6c0a4e266fcee3530addbc911901b54275fd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/app/office/md_wysiwyg_spec.spl
mirror: doc/06_spec/01_unit/app/office/md_wysiwyg_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/md_wysiwyg_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/md_wysiwyg_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/md_wysiwyg_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/office/md_wysiwyg_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has one row per source line' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/md_wysiwyg_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves the source in the source pane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/md_wysiwyg_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders styled HTML in the preview pane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
