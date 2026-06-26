# Spec: LLM Dashboard Tooling Artifact Collector

Source: `test/unit/app/llm_dashboard/collectors/tooling_artifact_collector_spec.spl`

## Behavior

- Mirrors collector coverage for readable files, text rendering, missing files,
  and HTML escaping.
- Keeps public output free of internal absence markers.

## Covered Requirement

- Mirrored unit evidence for the dashboard-facing context/ponytail artifact
  collector.

## Not Covered

- Persistent indexing or live browser/dashboard wiring.
