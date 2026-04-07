# Native Exe Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/app/native_exe_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 45 |
| Active scenarios | 45 |
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
| `result.json` | JSON artifact | `target/test-artifacts/feature/app/native_exe/result.json` |

## Scenarios

- creates config with entry point and output
- defaults to nil backend (SMF pipeline)
- defaults to PIE enabled
- defaults to optimization level 0
- defaults to libc as library dependency
- accepts llvm as backend value
- accepts smf as backend value
- uses x86-64-v3 as default target CPU
- includes standard libraries
- uses optimization level 2
- parses --backend=llvm
- parses --backend=smf
- detects unknown backend from flag
- dispatches to LLVM when backend is llvm
- dispatches to SMF when backend is nil
- dispatches to SMF when backend is smf
- contains module name comment
- declares __simple_runtime_init
- declares __simple_main
- declares __simple_runtime_shutdown
- defines main with argc and argv
- calls runtime init before main
- calls __simple_main and captures result
- truncates i64 result to i32 exit code
- returns exit code
- defines _start with noreturn
- contains halt loop
- uses hlt instruction in halt loop
- selects main for hosted mode
- selects _start for bare-metal mode
- declares __simple_runtime_init as void function
- declares __simple_runtime_shutdown as void function
- declares __simple_main as extern
- defines main that calls init, __simple_main, shutdown
- returns result from __simple_main
- generates C source path from output path
- generates object file path from output path
- source_to_smf_path converts .spl to .smf in .build
- source_to_obj_path converts .spl to .o in .build
- maps optimization 0 to Debug
- maps optimization 2 to Speed
- maps optimization 3 to Aggressive
- uses fixed path for entry point object
- converts module path to file path
- converts deep module path
