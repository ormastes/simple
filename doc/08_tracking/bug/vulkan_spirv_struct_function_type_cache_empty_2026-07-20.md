# Bug: Vulkan/SPIR-V backend struct+function type-key cache emits nothing
(expected cached `OpTypeStruct`/`OpTypeFunction` declarations, got `[]`)

**Status:** OPEN — filed, not fixed (source not read in depth)

**Date:** 2026-07-20
**Campaign:** whole-suite 01_unit triage (fix_guide.md)
**Severity:** Genuine logic bug — 1 of 17 examples blocked, pure
compile-time text-generation check (not GPU/hardware dependent, so not ENV)

## Symptom

```
BIN=/home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple
SIMPLE_RUST_SEED_WARNING=0 timeout 90 "$BIN" test \
  test/01_unit/compiler/backend/vulkan_backend_intensive_spec.spl \
  --no-session-daemon 2>&1 | sed 's/\x1b\[[0-9;]*m//g' | grep -A2 '✗'

Vulkan MIR backend intensive supported and fail-closed contract
✗ caches struct and function type keys without duplicate emission
  expected [] to equal [%1 = OpTypeStruct %7 %11, %2 = OpTypeFunction %1 %7 %11]
```

16 of 17 examples pass (including "emits an entry point and all GPU
invocation IDs without placeholders" in the same describe block), isolating
the defect to the struct/function type-caching path specifically.

## Root-cause hypothesis (not verified against source)

The actual value is an empty array `[]` where a 2-element array of emitted
SPIR-V type declarations (`OpTypeStruct`, `OpTypeFunction`) was expected —
this looks like either (a) the type-key cache is being queried/asserted
before the compile step that populates it runs, or (b) the dedup/cache-key
computation for struct+function types is failing to match on the intended
key and silently produces no emission (fail-open on a lookup miss) instead
of emitting the declarations once.

## Reproduction

`test/01_unit/compiler/backend/vulkan_backend_intensive_spec.spl`, example
"caches struct and function type keys without duplicate emission".

## Suggested follow-up

Read the Vulkan/SPIR-V backend's type-key caching code (likely under
`src/compiler/70.backend/backend/vulkan/` or similar) for how struct and
function `OpType*` declarations get accumulated/deduped, and compare against
this example's expected 2-line output.
