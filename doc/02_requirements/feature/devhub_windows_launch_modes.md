<!-- codex-design -->
# DevHub Windows launch modes

The user requested ordinary and loading startup on Windows. Recovery review
found no in-tree loader implementing the proposed external `--runtime`
contract. Loading remains **unimplemented**; recognizing its selection and
failing explicitly is a partial delivery, not an AV recovery feature.

- REQ-DHLM-001: Default/explicit ordinary mode uses the existing host and
  provenance admission and forwards application arguments unchanged.
- REQ-DHLM-002: Until an actual admitted loader exists, explicit loading mode
  fails with exit 78 before executing or probing any runtime or loader.
- REQ-DHLM-003: Neither selection silently falls back to another mode.
- REQ-DHLM-004: Ordinary dispatch reports mode, artifact, receipt, and version;
  unsupported and admission failures report the selected mode and next action.
- REQ-DHLM-005: Neither selection changes antivirus policy or exclusions.

Focused executable coverage: `test/00_unit/scripts/devhub_windows_launch_modes_test.shs`.
End-to-end loading and AV classification remain outstanding.
