# Scoped unsafe capability parser owner (2026-08-22)

## Symptom

The third source-matched native-build cycle reported 12 failed bodies in
`nogc_sync_mut/sffi/io.spl` and `nogc_sync_mut/sffi/system.spl`. Every detailed
diagnostic was identical:

```text
GlobalLoad: unresolved identifier 'ffi' (not a global, function,
const-data name, or import)
```

The authoritative retained log is
`build/native_probe/mcdc_source_matched_cycle3/build.time`, lines 161-184.

## Root cause and repair

These are not 12 independent SFFI ABI failures. Function declarations entered
`parse_block` through the legacy `compiler.core.parser_stmts` alias. That owner
can be absent from a restricted source closure, making
`unsafe(capabilities: [ffi]):` parse as ordinary expressions. The capability
name then escaped into MIR as a global load.

Commit `763457a1f113` binds function bodies to the canonical
`compiler.frontend.core.parser_stmts.parse_block` owner. Capability names are
consumed once as text and remain Flat-AST/HIR metadata; none is evaluated at
runtime. The optional-array, tuple, and scalar wrapper shapes now have a direct
AST regression in
`test/01_unit/compiler/frontend/scoped_unsafe_function_body_parser_spec.spl`.

## Performance and memory boundary

The repair changes one static import edge. It adds no runtime branch,
allocation, scan, or wrapper call. The bounded five-owner source gate completed
in 0.02 seconds with 2,304 KiB maximum RSS; evidence is retained in
`build/native_probe/mcdc_source_matched_cycle3/sffi-focused/ownership.log`.

No full build was repeated. The focused executable spec could not run because
this worktree has no admitted `bin/simple`; the retained Stage-2 executable is
a native-build-only CLI and rejects `test`. Its attempt is retained in
`build/native_probe/mcdc_source_matched_cycle3/sffi-focused/spec-stage2.log`.
Run the spec once with the next source-matched admitted Pure-Simple CLI.
