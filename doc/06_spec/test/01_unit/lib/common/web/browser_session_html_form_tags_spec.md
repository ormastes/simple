# Browser Session Html Form Tags Specification

> <details>

<!-- sdn-diagram:id=browser_session_html_form_tags_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_html_form_tags_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_html_form_tags_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_html_form_tags_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Html Form Tags Specification

## Scenarios

### BrowserSession HTML form tag text semantics

#### preserves visible label and option text across form container tags

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<form><fieldset><legend>Profile</legend><label>Name</label><select><optgroup label='Group'><option>One</option><option>Two</option></optgroup></select><datalist><option>Suggest</option></datalist><textarea>Notes</textarea><button>Save</button><output>Done</output></fieldset></form>"
expect(html_to_text(html)).to_equal("ProfileNameOneTwoSuggestNotesSaveDone")
```

</details>

#### extracts text from value-bearing form controls

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<form><input type='text' value='Alice'><input type='submit' value='Send'><progress value='7' max='10'></progress><meter value='3' min='0' max='5'></meter></form>"
expect(html_to_text(html)).to_equal("AliceSend7/103/5")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_html_form_tags_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserSession HTML form tag text semantics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
