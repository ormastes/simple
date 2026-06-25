# SPM pt-walk user-copy Requirements

Feature: FR-SPM-0001.

- REQ-SPM-0001-001: VMM must expose an explicit `ProcessVmSpace` user VA
  translation helper that returns nil on missing, non-user, or unreadable pages.
- REQ-SPM-0001-002: SPM `_copy_in_bytes` must use explicit-space page walking
  for real process vmspaces and return `[]` on any translation miss.
- REQ-SPM-0001-003: Grant `safecopy_from` and `safecopy_to` must reject real
  process vmspaces whose page tables do not translate the requested range.
- REQ-SPM-0001-004: Cross-page copy validation must fail when any touched page
  is not mapped for the requested access.
- REQ-SPM-0001-005: pml4-less unit-test and early-boot fixtures may keep the
  existing VMA-only behavior after range validation.
