# Seed `.?` bool-lowering crashes the CUDA arm of engine2d backend resolution

**Date:** 2026-08-02 · **Severity:** medium · **Area:** seed lowering of `.?` / engine2d CUDA probe

## Symptom

In the engine2d backend viable-probe path, the CUDA candidate arm crashes
under the seed lowering when an `.?` existence check on the CUDA
session/handle is involved: the seed lowers `.?` to a plain bool
(known family — see memory/bug note "Seed `.?` lowers to BOOL",
`reference_seed_exists_check_lowers_to_bool`), so code that then uses the
checked value as the original typed handle receives a bool and the CUDA arm
faults instead of being rejected cleanly.

## Expected

A failing/absent CUDA candidate must be REJECTED by the viable probe with a
`[backend-resolve] cuda rejected: <why>` line and fall through to the next
candidate — never crash the resolution.

## Workaround in tree

The landed resolver (engine.spl `probe_backend_viable`) avoids relying on
`.?`-checked handles in the seed-lowered path; rejection is derived from the
probe render round-trip result instead of an existence check.

## Status

The lowering defect itself remains open (family bug); the resolution path no
longer depends on it.
