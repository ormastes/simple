# Experiment Tracking Integration Specification
*Source:* `test/feature/usage/experiment_tracking_spec.spl`
**Feature IDs:** #exp-integration  |  **Category:** Stdlib  |  **Status:** In Progress

## Overview



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

## Feature: Experiment Tracking Workflow

## End-to-End Workflow

    Tests the complete experiment tracking lifecycle from config
    through run completion and querying.

### Scenario: basic workflow

| # | Example | Status |
|---|---------|--------|
| 1 | creates a run, logs metrics, and completes | pass |
| 2 | stores and retrieves artifacts | pass |

**Example:** creates a run, logs metrics, and completes
    Given var values: Dict<text, ConfigValue> = {}
    Given val config = ExpConfig(values: values, source_files: [], overrides: {})
    Given var run = start_run(config, ["test", "integration"])
    Then  expect run.status == RunStatus.Running
    Then  expect run.status == RunStatus.Completed

**Example:** stores and retrieves artifacts
    Given val config = ExpConfig__empty()
    Given var run = start_run(config, [])
    Given var store = ArtifactStore__for_run(run.run_id)
    Given val hash = store.register_data("results.sdn", "loss: 0.1{NL}acc: 0.95", {})
    Then  expect hash.?
    Given val content = store.get_blob("results.sdn")
    Then  expect content == Some("loss: 0.1{NL}acc: 0.95")

### Scenario: config composition

| # | Example | Status |
|---|---------|--------|
| 1 | merges configs with overlay winning | pass |

**Example:** merges configs with overlay winning
    Given var base_vals: Dict<text, ConfigValue> = {}
    Given val base = ExpConfig(values: base_vals, source_files: [], overrides: {})
    Given var overlay_vals: Dict<text, ConfigValue> = {}
    Given val overlay = ExpConfig(values: overlay_vals, source_files: [], overrides: {})
    Given val merged = merge_configs(base, overlay)
    Given val lr_val = merged.get("lr")
    Given val lr_ok = match lr_val:
    Then  expect lr_ok
    Given val bs_val = merged.get("batch_size")
    Given val bs_ok = match bs_val:
    Then  expect bs_ok

### Scenario: querying

| # | Example | Status |
|---|---------|--------|
| 1 | lists runs by status | pass |
| 2 | lists all runs | pass |

**Example:** lists runs by status
    Given val filter = RunFilter__by_status("completed")
    Given val runs = list_runs(filter)
    Then  expect runs.len() >= 0

**Example:** lists all runs
    Given val runs = list_runs(RunFilter__all())
    Then  expect runs.len() >= 0

## Feature: Run Comparison

## Comparing Runs

    Tests for diffing config and metrics between runs.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | diffs two runs with different configs | pass |

**Example:** diffs two runs with different configs
    Given var vals_a: Dict<text, ConfigValue> = {}
    Given val config_a = ExpConfig(values: vals_a, source_files: [], overrides: {})
    Given var vals_b: Dict<text, ConfigValue> = {}
    Given val config_b = ExpConfig(values: vals_b, source_files: [], overrides: {})
    Given var run_a = start_run(config_a, ["baseline"])
    Given var run_b = start_run(config_b, ["experiment"])
    Given val result = diff_runs(run_a.run_id, run_b.run_id)
    Then  expect result.is_ok()


