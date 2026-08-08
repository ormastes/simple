# BrowserSession HTML form text projection

> Projects the supported form-control fallback semantics to visible text. This

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# BrowserSession HTML form text projection

Projects the supported form-control fallback semantics to visible text. This

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_html_form_tags_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

Projects the supported form-control fallback semantics to visible text. This
is focused text-projection evidence, not form interaction or pixel evidence.

## Scenarios

### BrowserSession HTML form tag text semantics

#### should preserve visible label and option text across form containers

- Project supported HTML semantics to visible text
   - Expected: html_to_text(html) equals `ProfileNameOneTwoSuggestNotesSaveDone`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project supported HTML semantics to visible text")
val html = "<form><fieldset><legend>Profile</legend><label>Name</label><select><optgroup label='Group'><option>One</option><option>Two</option></optgroup></select><datalist><option>Suggest</option></datalist><textarea>Notes</textarea><button>Save</button><output>Done</output></fieldset></form>"
expect(html_to_text(html)).to_equal("ProfileNameOneTwoSuggestNotesSaveDone")
```

</details>

#### should extract text from value-bearing form controls

- Project supported HTML semantics to visible text
   - Expected: html_to_text(html) equals `AliceSend7/103/5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project supported HTML semantics to visible text")
val html = "<form><input type='text' value='Alice'><input type='submit' value='Send'><progress value='7' max='10'></progress><meter value='3' min='0' max='5'></meter></form>"
expect(html_to_text(html)).to_equal("AliceSend7/103/5")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
