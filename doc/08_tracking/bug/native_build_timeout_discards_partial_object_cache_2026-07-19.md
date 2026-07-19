# native-build timeout discards successfully compiled object cache

**Status:** NO-MANGLE SOURCE FIXED / DEPLOY QUALIFICATION PENDING  
**Severity:** P1 — prevents bounded incremental builds from converging  
**Owner:** `src/compiler_rust/compiler/src/pipeline/native_project/`

## Reproduction

Two cached Stage 2 v39 entry-closure builds of the full CLI each reached the
900-second timeout during code generation. The second build reused the same
cache but still did not produce a Stage 4 executable. This is incomplete
compilation, not a crash or orphaned-worker hang.

## Root cause

Successful objects were copied from the temporary staging directory into the
incremental cache only after every dirty module compiled successfully. A later
module failure or outer timeout therefore discarded reusable completed work.

## Solution

Dependency-independent `no_mangle`, non-entry, non-inline-assembly objects are
now persisted atomically to their final content-addressed cache path as soon as
they compile. Mangled builds retain whole-batch publication because their
objects depend on complete cross-module import context. Concurrent publication
is accepted only when the destination bytes match.

Cache keys now also include the effective codegen backend and optimization
level while preserving the existing compiler, target, SIMD, module-prefix, and
global-fingerprint inputs.

## Focused evidence

- optimization-level key separation: PASS
- backend key separation: PASS
- sequential and parallel fail/retry object reuse: PASS

An admitted Stage 4 rebuild and bounded retry remain required before production
deployment is qualified.
