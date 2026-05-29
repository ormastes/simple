# Experiment Tracking Integration Specification

**Feature ID:** #exp-integration | **Category:** Stdlib | **Difficulty:** 3/5 | **Status:** In Progress

_Source: `test/feature/usage/experiment_tracking_spec.spl`_

---

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

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 6 |

## Test Structure

### Experiment Tracking Workflow

#### basic workflow

- ✅ creates a run, logs metrics, and completes
- ✅ stores and retrieves artifacts
#### config composition

- ✅ merges configs with overlay winning
#### querying

- ✅ lists runs by status
- ✅ lists all runs
### Run Comparison

- ✅ diffs two runs with different configs

