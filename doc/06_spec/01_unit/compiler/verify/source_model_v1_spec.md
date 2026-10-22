# Source-to-Lean model worker APIs

Requirements: EE-01, REQ-MC-007, C2. Executable specification:
`test/01_unit/compiler/verify/source_model_v1_spec.spl`.

**15 scenarios authored; all UNRUN.** This manually maintained companion is not
a generated execution report. Compilation, SPipe execution, coverage,
generated-manual maintenance, Lean checking and proof replay remain pending.
The tests-first snapshot is retained in the EE-01 packet under
`cli-tests-first` before production implementation (12 initial scenarios).
The directory-qualified namespace regression was added after source review
identified the existing raw namespace interpolation boundary.

Use `simple gen-lean source-model FILE.spl TARGET_TRIPLE` to request an artifact.
The command requires exactly two operands, a regular source file, and an
explicit supported target. It reuses the existing source-call target and
transformation boundaries, canonical target-aware frontend, HIR lowering, the
opt-in enum semantic producer, and the full public Lean module exporter.

Successful output starts with `-- formal_status=NOT_CHECKED`, followed by the
source-text digest, target and actual frontend cfg digests as Lean comments,
then the exported Lean source. The text digest identifies decoded text passed
through the existing file facade; it is not a raw-file encoding attestation.
Output is returned only after complete module export succeeds. Errors return
nonzero without publishing a partial model.

| Scenario | Action | Required observation |
|---|---|---|
| Enum model | Parse `Flag.Off`/`Flag.On` match and export the full module | Both named variants and exact i32 constants appear, raw enum carrier helpers do not, unchecked status appears |
| Explicit target | Export target-conditional declarations for x86_64 and aarch64 | Each output includes only the constant selected by that target |
| Directory-qualified identity | Export a source path containing directories and a hyphen | Named enum output succeeds without a raw filesystem path in the Lean namespace |
| Missing or invalid target | Supply empty, host, native, malformed or ambiguous target | Existing target error occurs before parsing |
| Missing identity | Supply an empty source path to the source API | File-identity error |
| Malformed source | Parse an incomplete function declaration | Parser error and no model |
| Unresolved call | Lower an undeclared source callee | HIR error and no model |
| Import | Request a module requiring external dependency resolution | Driver-graph refusal |
| AOP transformation | Supply source advice requiring weaving | Existing transformation refusal |
| Atomic failure | Export a valid enum function followed by unsupported f64 | Export error without unchecked header or partial Lean model |
| Wrong arity | Supply zero, one or three operands | Usage error before file access |
| Missing file | Request a nonexistent path | File error |
| Directory | Use `src` as the input path | Regular-file admission error |
| Successful file worker | Allocate a unique private directory, exclusively create and check a regular source file whose name contains a space, call `source_model_command_v1` | Correct source digest, explicit target, unchecked enum model and exact constants; directory removed before assertions |
| Atomic file-worker refusal | Pass a checked regular file containing a valid enum function and a later unsupported f64 function | Export error without unchecked header or partial model; directory removed on refusal |

These worker oracles exercise actual source/backend APIs; the target scenario checks
frontend selection, while the producer's own specifications cover exact MIR
target-context propagation. The two file cases use `secure_temp_dir`,
`file_create_exclusive` and `file_is_regular_no_follow`; cleanup failure or a
remaining directory fails the scenario. The setup and command use the same
real filesystem; no file or process result is mocked.

This unit spec does not launch an external CLI process. Actual dispatcher,
delegation, exit and output behavior are separately specified in
`test/03_system/app/gen_lean/feature/source_model_command_spec.spl` and its
manual under `doc/06_spec/03_system/app/gen_lean/feature/`. All worker and command
scenarios remain UNRUN; none establishes compiler execution, Lean checking,
native output or a release gate. Existing gen-lean
modes retain their worker routing. Full C1 transformed-source provenance,
C6 authentication/replay and C7 physical refinement remain open.
