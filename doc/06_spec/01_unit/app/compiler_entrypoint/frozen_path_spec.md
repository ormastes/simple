# Compiler frozen source path mapping

Executable: `test/01_unit/app/compiler_entrypoint/frozen_path_spec.spl`.
Scope: seven-plan item 1 host-path parity.
This is a manually maintained scenario companion; production docgen is pending.

| Scenario | Steps | Outcome |
|---|---|---|
| Map an existing source | Resolve a real repository file; resolve repository root | Both map beneath the admitted snapshot root |
| Reject unavailable authority | Resolve parent directory outside root; use invalid admission or empty path | No frozen path is returned |
| Preserve frozen identity | Temporarily bind an existing frozen root; resolve its existing file; restore environment | Path remains unchanged and all environment writes succeed |

Initial Windows Phase-1 diagnostic execution passed 3/3 on unchanged production
code. This runtime returned plain Windows paths rather than verbatim paths;
the hypothesized native prefix regression was not reproduced.
The Windows verbatim-input row is maintained separately in
`test/01_unit/app/compiler_entrypoint/frozen_path_windows_spec.spl` and its
matching manual. The common spec retains only the three portable scenarios.
