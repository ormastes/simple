# Structured compiler diagnostic capture manual

Status: authored UNVERIFIED / NOT_RUN; not generated execution evidence.

Executable: `test/01_unit/compiler/driver/structured_diagnostic_capture_v1_spec.spl`.

Cases retain an original rich record containing children, cross-file labels, macro trace and a replacement fix; refuse uncaptured legacy errors/direct warnings and advisory-only messages; reject invalid coverage; preserve exact HM byte ranges and related files; invoke real parsing/lowering/HM warning consumption; and reject zero-diagnostic completion when collection or required producer inventories are missing.

Run once with the admitted self-hosted runtime after compiler prerequisites. Native archive/scratch/session teardown and immutable multi-file snapshot tests are additional required gates; these unit cases do not certify them. Do not promote authored assertions or static whitespace checks to PASS.
