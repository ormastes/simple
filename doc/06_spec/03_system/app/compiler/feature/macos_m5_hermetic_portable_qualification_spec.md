# M5 Hermetic Portable Qualification

- Executable: `test/03_system/app/compiler/feature/macos_m5_hermetic_portable_qualification_spec.spl`
- Requirements: `MBH-REQ-007`, `MBH-NFR-004`
- Evidence class: executable SPipe definition; runtime PASS is not claimed.

## Scenario

### executes the focused M5 checker only from an immutable snapshot

The driver snapshots itself, admits the exact three-file M5 closure, records
source and snapshot inventories, runs with an isolated environment, and rejects
source or snapshot drift before retaining the final receipt.

Native slices, signing/notary services, commit, deployment, and promotion are
outside this portable structural scenario.
