# Seed compile aborts on `namespace` used as a Simple identifier

Date: 2026-09-17
Lane: kimi-20260915-beta2 (v1.0.0-beta.8 -> beta.9)
Run: release run 35199250249 (v1.0.0-beta.8), windows-x86_64 blocking leg

## Symptom

The beta.8 release leg reached module compilation and died with:

```
error: Common mistake detected: See error message for details
  --> src/app/build/targets/action_identity.spl:368:8
368 |     if namespace.len() == 0 or ...
    |        ^
Use 'mod' for modules instead of 'namespace'.
```

`namespace` is a legal Simple identifier and is used as a local variable in
at least six files (`action_identity.spl`, `artifact_receipt.spl`, two
portal controllers, `spec_to_spipe/model/contracts.spl`,
`alloc_diagnostic_config.spl`). The standard CI never compiles these under
the seed's release entry closure, so the defect only surfaced in the
release run's `bootstrap_main` `--entry-closure` compile.

## Root cause

`src/compiler/10.frontend/parser/recovery.spl` flagged the lexeme
`namespace` unconditionally (`if current_lexeme == "namespace" ... return
CppNamespace`), unlike its sibling detectors (`interface`, `template`,
`function`, `public`) which guard on surrounding tokens. Any identifier
named `namespace` produced the C++ recovery hint; under the seed-run
release compile the hint is emitted at error severity and aborts the build.

## Fix

Guard `CppNamespace` on the declaration shape only: fire when the next
token is an Identifier (`namespace <ident>`, the C++ form). Dotted access,
calls, and binders (`namespace.len()`, `val namespace = ...`) no longer
trigger it. Mirrors the existing `TsFunction` guard pattern.

## Notes

- The linux-x86_64 blocking leg was cancelled externally for the third time
  (beta.8: 10:35-10:46Z, ~12 min into the seed build, despite the new
  progress echo). Cause unknown; not a GitHub mechanism (no cancel job,
  fail-fast false, cancel-in-progress false). Needs owner input.
- Sibling detectors audited: `this`/`void`/`const`/`function` only appear in
  comments or string literals in src/; `template` is already guarded.
