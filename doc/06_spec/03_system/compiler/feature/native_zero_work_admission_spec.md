# MBH-NFR-002 Native Zero-work Admission

- Executable: `test/03_system/compiler/feature/native_zero_work_admission_spec.spl`
- Requirement: `MBH-NFR-002`
- Evidence class: executable native SPipe plus production native-build process probes.

## Scenarios

- Admit unchanged bounded inputs before any compiler scheduler work.
- Fail closed on source, output, provenance, and interrupted pointer changes.
- Reject stale invocation/requested-input identity and missing/corrupt current generations.
- Recursively reject a deleted or corrupt non-current ancestor.
- Preserve collision evidence and recover an unselected immutable generation name.
- Miss when canonical no-mangle, package-index, safety/type, or linker controls change.
- Reject an unknown or omitted centralized environment-schema field.
- Distinguish absent, present-empty, and present-valued unknown `SIMPLE_*` controls.
- Audit all owned compiler/lib/runtime/native CLI environment-read names against
  a generated count and digest so newly introduced fields fail CI review.
- Kill the native publisher at generation and pointer write/rename/fsync boundaries;
  recovery must retain the old complete state or the new complete state.

## Pass criteria

The second production `native-build` prints one authenticated admission receipt
whose actual scheduler counters are exactly
`parser=0 hir=0 mir=0 codegen=0 link=0`. Every mutation is a miss or an
attributed publication failure. If no compatible self-hosted native runtime is
available, execution is `BLOCKED`; source inspection is not a substitute.

The executable source contains real assertions and no `pass_todo` or
tautological placeholder pass.
