# TLDR interface stub splits attributes on ';' -> `[parser_error] unexpected token in expression: ->`

- **Status:** verification-pending
- **Found:** 2026-11-21, phase-2 xc matrix `linux-x64-test` log (~44k `[parser_error]` lines), e.g.
  `line 42:54: unexpected token in expression: ->` in `std/nogc_sync_mut/io/dir_ops.spl`; also `secure_memory.spl`, `sha256.spl`.

## Cause
Not a tuple-return parse gap. The line numbers are in the TLDR interface
*stub* (`module_surface_tldr_stub_source_v1`), not the source. The summary
row stores a declaration's attributes joined with `;`
(`cfg=<a1>;<a2>`), and the stub builder split on every `;`. dir_ops'
`@unsafe(reason: "raw directory-create ABI; false is ...", capabilities: [ffi])`
was cut into two lines, so the following `extern fn rt_dir_create(...) -> bool`
was parsed in expression context and failed at `->`. The stub surface then
lost those externs (fallback to source load).

## Fix
`src/compiler/20.hir/hir_lowering/module_surface_from_tldr_v1.spl`: a split
piece that does not start with `@` is re-joined to the previous attribute.
Summary format unchanged.

## Tests
`test/01_unit/compiler/driver/module_surface_from_tldr_spec.spl` — "TLDR stub
keeps attributes whose text contains ';'" (red before, green after).
Pre-existing, unrelated failure in the same file: "treats cfg-attributed
declarations exactly like the source surface" (callable order sorted vs
source order) fails on the base too.
