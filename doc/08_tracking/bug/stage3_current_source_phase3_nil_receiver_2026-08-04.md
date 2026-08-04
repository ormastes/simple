# Current-source Stage 3 traps at HIR/typecheck entry

## Status

Fixed at the exact crash boundary by the Clang 23.1 browser-demo migration
lane. Stage 3 remains unavailable because the same final bounded build exposed
a later, separately tracked VHDL enum-owner conflict.

## Exact reproduction

At source revision `4ad6f949e9241ed445d635cf33195f9eb1897065`, the admitted
Stage 2 compiler
`build/bootstrap/stage3/aarch64-apple-darwin/stage2-admitted/simple`
(SHA-256 `725bc93647f25f2ed839c611c439034f2cab758f54bc1c21c4fbb2bc5a16e9e2`)
runs the transcribed Cranelift `native-build` for
`src/app/cli/bootstrap_main.spl` with stub fallback disabled and exits 132:

```text
phase2:parse:done n_modules=804 heap_registry=57529406
phase3:hir_typecheck:start heap_registry=57529458
runtime error: field access on nil receiver
```

The default run is retained in
`build/bootstrap/logs/aarch64-apple-darwin/stage3-native-build.log` and the
direct debug replay in `build/native_probe/stage3-diagnostic/run.log` plus
`progress.events`. The replay proves all 542 closure sources and 804 parsed
modules completed before the trap; no diagnostic Stage 3 binary was emitted.

## Ownership boundary

The defect is currently owned by the pure-Simple driver/HIR handoff. The first
suspect boundary is `CompilerDriver.lower_and_check_impl`, including transport
of `CompileContext`, `SourceFile`, parsed-module dictionaries, and
`module_surfaces_from_modules`. Rust/runtime changes are forbidden unless a
debugger proves the pure layer delegates a valid value below that boundary.

This resembles, but is not assumed identical to, the resolved
`bootstrap_stage3_module_surface_placeholder_nil_2026-08-01` dictionary/value
transport failure. The current incident occurs before the first retained
per-module HIR marker and therefore requires a fresh stack/boundary receipt.

## Required regressions

1. Exact: the same current-source Stage 2-to-Stage 3 command reaches HIR module
   progress and emits a valid Stage 3 candidate with no nil-receiver trap.
2. Adjacent: a focused native regression transports the parsed
   `CompileContext` into HIR setup and validates multiple early source/module
   identities plus module-surface extraction, covering the prior source-index-6
   dictionary failure family.

The shared bootstrap/provider/QEMU lane retains its three-cycle cap. The debug
replay is diagnostic evidence only and cannot admit Stage 3 or Stage 4.

## Root cause and bounded result

LLDB stopped in
`compiler.frontend.parser_types_expr.parser_type_kind_array_element_name`.
The helper decoded tuple payload slot zero for every `TypeKind` without first
proving the value was `TypeKind.Array`; an ordinary named type from module
surface extraction was therefore reinterpreted as a `Type` and trapped on
`element.kind`.

Both parser-owned array helpers now compare the typed discriminant with an
`Array` reference before reading the payload. The existing Stage 4 parser/HIR
boundary probe covers a real array plus the adjacent non-array fallback and
empty-name behavior. Bootstrap-seed syntax checks passed for the owner and
probe.

Final-cycle evidence is retained in
`build/bootstrap-clang-23-1-stage4-current-cycle3.out` and
`build/bootstrap/logs/aarch64-apple-darwin/stage3-native-build.log`. It proves:

- Stage 2: 726 compiled, zero cached, zero failed; sanity passed.
- Stage 3: 542/542 sources parsed and every HIR module completed.
- The former nil-receiver and SIGILL did not recur.
- Stage 3 then failed normally in monomorphization on the distinct
  `VhdlProcessKind` owner conflict recorded in
  `stage3_vhdl_process_kind_enum_payload_conflict_2026-08-04.md`.

No Stage 3 or Stage 4 candidate was emitted, so the exact native probe remains
pending behind that later blocker. Do not represent the syntax check as native
runtime evidence.
