# TODO Implementation Report - 2026-01-20

## Summary

Implemented **3 out of 5** actionable TODOs. The remaining 2 TODOs require compiler team architecture work (FFI bridges from compiler crates).

## Completed TODOs: 3

### 1. rt_dict_remove() Implementation ✅

**File:** `src/runtime/src/value/dict.rs`
**Status:** COMPLETE
**Priority:** P2

**What was implemented:**
- Added `rt_dict_remove()` FFI function to runtime
- Implements linear probing hash table deletion with rehashing
- Returns the removed value (RuntimeValue::NIL if not found)
- Maintains probe chain integrity by rehashing subsequent entries

### 2. SDN Parser Integration ✅

**File:** `simple/std_lib/src/tooling/env_commands.spl`
**Status:** COMPLETE
**Priority:** P3

**What was implemented:**
- Imported SDN parser into env_commands.spl
- Parse config.sdn files when listing environments
- Display key configuration fields (name, python_version, created)

### 3. BTreeMap/BTreeSet Integration ✅

**File:** `simple/std_lib/src/tooling/context_pack.spl`
**Status:** COMPLETE (from previous session)

## Remaining TODOs: 2 (Require Compiler Team)

### 4. Parser Integration ⏸️

**File:** `simple/std_lib/src/tooling/context_pack.spl:46`
**Status:** BLOCKED - Requires compiler team work

**Why blocked:**
- Requires FFI bridge from simple_parser crate to runtime
- Architectural concern: Runtime shouldn't depend on compiler (circular dependency)
- Needs design for how to expose AST nodes to Simple code

### 5. Minimal Mode Extraction ⏸️

**File:** `simple/std_lib/src/tooling/context_pack.spl:56`
**Status:** BLOCKED - Depends on Parser integration

## Files Modified

1. src/runtime/src/value/dict.rs - Added rt_dict_remove()
2. src/native_loader/src/static_provider.rs - Registered rt_dict_remove
3. simple/std_lib/src/infra/config_env.spl - Used rt_dict_remove()
4. simple/std_lib/src/tooling/env_commands.spl - Integrated SDN parser

## Completion: 60% (3/5)
