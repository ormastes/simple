# Image-to-Markdown dataset contract

Use stable headings in this order when sections apply:

1. `# Image dataset`
2. `## Source and provenance`
3. `## Page inventory`
4. `## Text and handwriting`
5. `## Tables and forms`
6. `## Charts and graphs`
7. `## Additional region content`
8. `## Unresolved content`

Tables should use ordinary Markdown tables where row/column topology permits it. Describe merged cells, highlights, handwriting, checkboxes, and source bounds adjacent to the table. Never fill a blank cell merely to make the table rectangular.

Render region manifests and additional region bodies by source page, then
declared reading order, then stable region ID. Do not trust provider array order.

For every chart, state panel ID, chart type, title, axes, scale, units, legend, and extraction limits. Include a fenced `json` block with this conceptual shape:

```json
{
  "panel_id": "panel-1",
  "series": [{
    "name": "visible legend text",
    "points": [{
      "x_lexeme": "1.00",
      "y_lexeme": "2.50",
      "x": 1.0,
      "y": 2.5,
      "status": "observed",
      "uncertainty_milli": 25,
      "uncertainty_low": 2.4,
      "uncertainty_high": 2.6,
      "source_box": [0, 0, 0, 1, 1]
    }]
  }]
}
```

`status` is one of `observed`, `calibrated`, `missing`, or `ambiguous`. A value inferred from curve height or pixel calibration is `calibrated`, never `observed`. Use `null` numeric values for missing or unresolved points and retain the visible lexeme when one exists.

Every compact source box is `[page_index,x,y,width,height]` in source-image
pixels. `uncertainty_milli` ranges from 0 through 1000; calibrated points also
carry numeric lower and upper bounds plus their calibration method.

The separate receipt binds source and result hashes to model/provider identity, model revision if known, profile fingerprint, receipt/extraction/prompt/preprocessing/renderer versions, image dimensions, timings, retry count, warnings, and final status. Never include API keys, raw credentials, or image data URLs.
