# Interpreter FFI bridge legacy syntax blocks source check
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** Open compiler/source migration blocker  
**Observed:** 2026-08-26  
**Path:** `src/app/interpreter/ffi/bridge.spl`

## Evidence

The self-hosted entrypoint reports the bootstrap-seed warning and rejects the
unchanged beginning of this file before reaching the SFFI hardening edit:

```text
line 5: unexpected token `..` in `from ..core import ...`
line 14: unexpected token `:` in the Rust-like struct field declaration
24 parser errors total
```

The same lines are present in `origin/main`; the hardening change only removes
the dead private block beginning after `NativeValue`.  The package initializer
checks successfully, and the optimizer can analyze the bridge, but neither is
a substitute for a clean direct source check.

## Required fix

Migrate the surviving typed native registry and value bridge to canonical
Simple syntax, preserving its public `call_native`, `register_native`, and
`NativeFunction` API and adding focused SPipe coverage.  Do not restore the
deleted generic all-`u64` dynload dispatcher as a workaround.

## Performance constraint

Preserve average O(1) registry lookup.  Do not add per-call library lookup,
symbol lookup, signature parsing, generic marshalling, or extra value copies.

## Addendum 2026-11-11 — lane interp5 verdict: SUPERSEDED

Verdict: **SUPERSEDED** by commit `9e7e7a526edb43ab29171d920449367e5fd48127`
(2026-11-07, PR #7597 "hir-nominal-generic-owner-20261107"), an ancestor of base
`b364745fdbf8`. That merge introduced the current 40-line
`src/app/interpreter/ffi/bridge.spl`, a complete migration to canonical Simple
syntax — the legacy `from ..core import ...` and Rust-like struct-field
declarations are gone. The required public API is preserved verbatim:
`export call_native, register_native, has_native, NativeFunction,
NativeRegistry`. The performance constraint holds: the registry is a
`Dict<text, NativeFunction>` with one probe per call and no per-call library /
symbol lookup, signature parsing, or value copying (stated in the file header
and visible in the source). The deleted generic all-`u64` dynload dispatcher was
not restored. Focused SPipe coverage exists at
`test/01_unit/app/interpreter/ffi_bridge_registry_spec.spl`.

Seed-smoke verification (2026-11-11, lane interp5, refreshed seed
`bin/simple.exe` 2026-11-11 build, `SIMPLE_LIB=src`):

- `bin/simple.exe check src/app/interpreter/ffi/bridge.spl` — the 24 legacy
  parser errors no longer occur; **zero** `unexpected token` errors. Parse
  succeeds. (Honest note: the isolated single-leaf check now stops later, at
  HIR lowering, with "missing module surface for app.interpreter.core" — the
  seed check does not pull the dependency closure for one leaf file. That is a
  check-harness scoping limitation, a different matter from the legacy-syntax
  blocker this bug tracked; CI checks whole app trees, e.g. `check src/app/mcp`.)
- `bin/simple.exe test test/01_unit/app/interpreter/ffi_bridge_registry_spec.spl
  --mode=interpreter --no-cache` → 3 total / 3 passed.

No further action for this bug. If the single-leaf module-surface limitation
matters, that is a new check-harness issue, not this one.

