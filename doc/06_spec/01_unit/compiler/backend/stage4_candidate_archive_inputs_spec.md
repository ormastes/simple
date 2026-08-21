# Stage4 candidate archive input contracts

Mirror of `test/01_unit/compiler/backend/stage4_candidate_archive_inputs_spec.spl`.

The executable SSpec checks acceptance of explicit Unix and Windows static-archive inventories and fail-closed rejection of incomplete, ambiguous, or forbidden inventories.

The assertions validate candidate-selection contracts in source; they do not link every accepted archive on each host platform.
