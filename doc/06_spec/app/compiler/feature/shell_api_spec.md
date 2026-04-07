# Shell Api Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/app/shell_api_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Documentation was generated from executable SSpec scenarios.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/app/shell_api/result.json` |

## Scenarios

- execute_command_basic
- execute_command_with_args
- execute_command_capture_stderr
- read_file_contents
- write_file_contents
- append_to_file
- check_file_exists
- list_directory
- list_directory_with_pattern
- create_directory
- remove_directory
- join_paths
- get_basename
- get_dirname
- get_extension
- absolute_path
- get_environment_variable
- set_environment_variable
- command_failure_result
- file_not_found_error
- pipe_commands
- chain_operations
- find_files_recursive
- copy_file
- move_file
