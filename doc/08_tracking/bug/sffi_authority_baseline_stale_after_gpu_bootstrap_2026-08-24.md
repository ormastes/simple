# SFFI authority baseline stale after GPU/bootstrap sync

**Date:** 2026-08-24  
**Status:** OPEN — concurrent owner follow-up required  
**Introduced by:** `54438b77546` (`fix(gpu,bootstrap): route dynamic probes and resume admitted stage2`)

## Evidence

One current-tree run of:

```text
scripts/audit/sffi-call-authority-census.shs --summary /tmp/sffi-dynamic-summary.tsv
```

reported:

```text
19504 missing
1712 lexical_unsafe
508 function_unsafe
SFFI call authority census: FAIL (19504 > 19503 raw call sites lack explicit FFI authority)
```

The committed ratchet remains `19503`. The upstream commit added a second
direct `rt_file_read_text("src/runtime/runtime_native.c")` call at
`test/01_unit/compiler/backend/stage4_runtime_native_wiring_spec.spl:23`
without a lexical `unsafe(ffi)` boundary. The pre-existing call at line 8 has
the same shape.

## Required resolution

The owner of the Stage-4 runtime wiring spec should replace direct runtime
access with the canonical file-reading facade when available, or add the
smallest honest lexical FFI boundary. Then run the authority census once and
update the ratchet only if the remaining debt is reviewed. Do not increase the
baseline merely to make the gate green.

This blocker is separate from the dynamic-loader checked migration. That slice
adds no new `rt_*` or `spl_*` call site and does not own the concurrent Stage-4
spec.
