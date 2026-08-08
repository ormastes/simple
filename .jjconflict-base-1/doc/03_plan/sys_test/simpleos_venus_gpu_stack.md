# SimpleOS Venus GPU stack system-test plan

| Requirement | Scenario/evidence |
|---|---|
| REQ-SVG-001/006 | Provider remains discovery-only and compositor unavailable. |
| REQ-SVG-002 | Valid PCI chain plus loop, short cap, reserved BAR, and overflow rejection. |
| REQ-SVG-003 | Stable DEVICE_CFG read plus three-retry stale-generation failure. |
| REQ-SVG-004 | shmid 1 selection, duplicate ID, missing region, and containment rejection. |
| REQ-SVG-005/007 | Zero/one/many/64 capsets; 65 rejected; partial response; payload 4072/4073 boundary. |
| REQ-SVG-008 | x86_64/AArch64/RISC-V adapters yield the same transport receipt schema. |
| REQ-SVG-009 | Future submit cannot be constructed before context/blob/ring receipts. |
| REQ-SVG-010/011 | Normalize equal semantic traces despite different raw handles/timestamp origins; reject unknown schema, drops, missing map, order and scalar/digest divergence. |
| REQ-SVG-012/013 | Compiled dynload success plus missing library/symbol, foreign error, use-after-close, double-close, and exactly-once reverse teardown. |
| REQ-SVG-014 | Each x86_64/AArch64/RISC-V expectation profile binds its canonical UI profile and rejects wrong transport/device/oracle/fallback/readback provenance. |
| REQ-SVG-015 | GPU and Chrome/Web specs import the generic comparator independently; a source/import contract rejects cross-domain production imports. |
| REQ-SVG-016 | Dependency/source audit proves no vendored VUDA or production import; optional external fixture is labelled non-render evidence. |

Executable specs belong under `test/01_unit/os/drivers/virtio/` for pure
decoders and `test/03_system/os/qemu/` for live guest evidence. The live manual
steps are frozen as: `Inspect bounded device capabilities`, `Enumerate capset
tuples`, `Confirm discovery-only admission`, and later `Submit and fence one
DrawIR frame`, `Read back and correlate device pixels`. Until the latter two
are implemented, their helpers must fail explicitly and cannot satisfy PASS.

Coverage is reported as measured branch coverage when supported; otherwise a
branch ledger lists valid/reject pairs. Example counts alone are not coverage.

Differential results supplement, never replace, the live QEMU chain. A matching
Mesa trace without guest boot/device-origin readback remains test-only oracle
evidence. ABI/error/ownership cases must execute in compiled mode; interpreter
results are recorded separately and cannot satisfy the compiled gate.
