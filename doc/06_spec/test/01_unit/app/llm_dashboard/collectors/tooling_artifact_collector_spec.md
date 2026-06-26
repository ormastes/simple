# Spec: LLM Dashboard Tooling Artifact Collector

Source: `test/01_unit/app/llm_dashboard/collectors/tooling_artifact_collector_spec.spl`

## Behavior

- Summarizes context pack stats and ponytail audit status for a readable file.
- Renders a text panel with context status, line/token counts, ponytail status,
  ponytail reason, and context preview.
- Renders missing files as explicit absence.
- Escapes HTML panel fields and previews.
- Keeps public output free of internal absence markers.

## Covered Requirement

- The dashboard can surface context/ponytail artifacts through a collector API
  without adding a second context or ponytail implementation.

## Not Covered

- Persistent context index/query.
- Full dashboard routing or browser integration.
