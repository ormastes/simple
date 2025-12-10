# Feature 103: Codegen Parity Completion

**Importance:** 5/5  
**Difficulty:** 5/5  
**Status:** PARTIAL

## Goal
Eliminate interpreter-only stubs and reach behavioral parity between compiled and interpreted execution across actors/futures/generators, collections, strings, structs/enums, methods, and outlined bodies.

## Current State
- Outlined body plumbing exists: functions are cloned, ctx captures packed/unpacked, reachable blocks retained.
- Actors/futures/generators pass outlined bodies and ctx to runtime; captures load in outlined entry.
- Many codegen areas remain stubbed or fallback to interpreter (collections, strings, enums, patterns, methods, async/state machines).

## Gaps
- Generator state machine not implemented (#101).
- Futures still eager/NIL (#102).
- Collections/strings/structs/enums/methods have stubbed or partial codegen paths.
- No compiled coverage tests exercising outlined actors/generators/futures.

## Next Steps
1) Finish capture parity (tests) and state machines (#100/#101/#102).  
2) Replace remaining stubs with real codegen/FFI calls for collections/strings/structs/enums/methods.  
3) Add compiled integration tests mirroring interpreter suites to validate parity. 
