# SPM pt-walk user-copy System Test Plan

Feature: FR-SPM-0001.

- `test/system/simpleos_spm_pt_walk_copy_spec.spl` covers the SPM-facing
  explicit-space copy contract.
- Required scenarios:
  - nil for unmapped user pointer
  - nil for execute-only VMA
  - false for cross-page range with an unmapped tail
  - EFAULT for copy-in translation miss
