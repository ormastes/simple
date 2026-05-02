# Experiment Tracking Integration Specification

Integration tests for the full experiment tracking workflow: config loading, run lifecycle, metric logging, artifact storage, and querying.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #exp-integration |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | In Progress |
| Source | `test/feature/usage/experiment_tracking_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Integration tests for the full experiment tracking workflow:
config loading, run lifecycle, metric logging, artifact storage,
and querying.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Run | A single experiment execution with config + metrics |
| Artifact | Content-addressed file stored with a run |
| Sweep | Hyperparameter optimization across multiple runs |
| Config | SDN-based configuration with composition and overrides |

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/experiment_tracking/result.json` |

## Scenarios

- creates a run, logs metrics, and completes
- stores and retrieves artifacts
- merges configs with overlay winning
- lists runs from empty state
- filters runs by completed status
- diffs two runs with different configs
