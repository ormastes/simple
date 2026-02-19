# Native Executable Generation Specification

**Feature ID:** #5000 | **Category:** Infrastructure | **Difficulty:** 4/5 | **Status:** In Progress

_Source: `test/feature/app/native_exe_spec.spl`_

---

## Overview

The native executable generation pipeline compiles Simple source files into
standalone native binaries. It supports two backends:
- **SMF pipeline**: Source -> SMF -> native via mold (existing)
- **LLVM pipeline**: Source -> MIR -> LLVM IR -> .o -> native via linker

## Key Concepts

| Concept | Description |
|---------|-------------|
| BuildConfig | Configuration for native builds (entry point, output, backend) |
| LLVM Backend | Compiles via MIR -> LLVM IR -> object code -> linked binary |
| SMF Backend | Compiles via SMF format -> native linking |
| Entry Point | Generated LLVM IR that bridges OS entry to Simple main |
| Runtime Stub | C stub providing __simple_runtime_init/shutdown + main |

## Behavior

- BuildConfig.backend selects the compilation pipeline ("llvm" or nil/smf)
- --backend=llvm CLI flag activates LLVM backend in handle_build_command
- Entry point IR generates proper main() or _start() functions
- Runtime stub compiles a C file with init/shutdown wrappers
- Object files are placed in .build/ directory

## Implementation Notes

- LLVM backend requires llc to be installed
- Runtime stub requires cc (gcc/clang) for compilation
- Entry point supports both hosted (main) and bare-metal (_start) modes

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 45 |

## Test Structure

### BuildConfig

#### default configuration

- ✅ creates config with entry point and output
- ✅ defaults to nil backend (SMF pipeline)
- ✅ defaults to PIE enabled
- ✅ defaults to optimization level 0
- ✅ defaults to libc as library dependency
#### LLVM backend configuration

- ✅ accepts llvm as backend value
- ✅ accepts smf as backend value
#### for_simple_cli configuration

- ✅ uses x86-64-v3 as default target CPU
- ✅ includes standard libraries
- ✅ uses optimization level 2
### LLVM Backend Flag Parsing

#### backend flag parsing

- ✅ parses --backend=llvm
- ✅ parses --backend=smf
- ✅ detects unknown backend from flag
#### backend dispatch logic

- ✅ dispatches to LLVM when backend is llvm
- ✅ dispatches to SMF when backend is nil
- ✅ dispatches to SMF when backend is smf
### Entry Point IR Generation

#### hosted entry point (main)

- ✅ contains module name comment
- ✅ declares __simple_runtime_init
- ✅ declares __simple_main
- ✅ declares __simple_runtime_shutdown
- ✅ defines main with argc and argv
- ✅ calls runtime init before main
- ✅ calls __simple_main and captures result
- ✅ truncates i64 result to i32 exit code
- ✅ returns exit code
#### bare-metal entry point (_start)

- ✅ defines _start with noreturn
- ✅ contains halt loop
- ✅ uses hlt instruction in halt loop
#### entry point mode selection

- ✅ selects main for hosted mode
- ✅ selects _start for bare-metal mode
### Runtime Stub Generation

#### stub C source content

- ✅ declares __simple_runtime_init as void function
- ✅ declares __simple_runtime_shutdown as void function
- ✅ declares __simple_main as extern
- ✅ defines main that calls init, __simple_main, shutdown
- ✅ returns result from __simple_main
#### stub file paths

- ✅ generates C source path from output path
- ✅ generates object file path from output path
### Build Pipeline Configuration

#### SMF pipeline (default)

- ✅ source_to_smf_path converts .spl to .smf in .build
#### LLVM pipeline

- ✅ source_to_obj_path converts .spl to .o in .build
- ✅ maps optimization 0 to Debug
- ✅ maps optimization 2 to Speed
- ✅ maps optimization 3 to Aggressive
#### entry point object file

- ✅ uses fixed path for entry point object
#### module path conversion

- ✅ converts module path to file path
- ✅ converts deep module path

