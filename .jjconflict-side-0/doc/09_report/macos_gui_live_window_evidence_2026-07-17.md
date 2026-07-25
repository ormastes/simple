# macOS GUI Live Window Evidence

The default is now the real Simple Web/winit host at
`src/app/ui_shared_mdi/live_window.spl`, not the IPC-only producer. During this
bounded attempt the GUI driver emitted 9,977 dependency advisory lines and did
not reach native window creation within 45 seconds. The failure below is
retained as evidence; no fourth live-window attempt was made.

The next bounded run uses a stronger source contract than this retained raw
failure: only completed primary-button releases can satisfy titlebar/body click
receipts, and initial, updated, or periodic winit presentation failure exits
nonzero before positive updated event evidence is persisted. The pure click
policy passes 6/6, the winit invalid-handle/present guard passes 4/4, and the
macOS source gate passes 7/7; none of those source checks promote this report to
a live-window PASS.

Presentation status also reaches the audited sibling hosts: Chromium retains
dirty state and returns failure, markdown GUI exits nonzero, and Game2D closes
its window. Their focused source contract passes 3/3; this remains supporting
source evidence rather than a replacement for the missing live macOS artifact.

- GUI SMF artifact contract status: missing
- GUI SMF artifact contract row: GUI_SMF_ARTIFACT_CONTRACT status=missing artifact=build/gui/pure_gui_hot.smf sha256= size=0 smf_role=-1 arch=0 embedded_dynlib=false symbol=gui_dynlib_hot_probe_tick qemu_status=not-run qemu_reason=live-qemu-not-executed macos_status=not-run macos_reason=requires-macos-arm64
- GUI SMF artifact contract scope: contract-only; does not promote live macOS window evidence
- Shared MDI titlebar contract status: pass
- Shared MDI titlebar sample: src/app/ui_shared_mdi/live_window.spl
- Native titlebar-control clicks: 0
- Native body-control clicks: 0
- Rendered completed-event counter pixels: 0

## Raw Evidence

- macos_gui_live_window_evidence_status=fail
- macos_gui_live_window_evidence_reason=window-not-found
- macos_gui_live_window_evidence_host_os=macos
- macos_gui_live_window_evidence_launcher=macos-gui-run
- macos_gui_live_window_evidence_simple_bin=/Users/ormastes/simple/bin/simple
- macos_gui_live_window_evidence_simple_bin_source=explicit-deployed
- macos_gui_live_window_evidence_simple_bin_status=pass
- macos_gui_live_window_evidence_sample=src/app/ui_shared_mdi/live_window.spl
- macos_gui_live_window_evidence_mdi_titlebar_contract_status=pass
- macos_gui_live_window_evidence_mdi_titlebar_button_markup_present=true
- macos_gui_live_window_evidence_mdi_titlebar_input_markup_present=true
- macos_gui_live_window_evidence_mdi_body_button_markup_present=true
- macos_gui_live_window_evidence_mdi_body_input_markup_present=true
- macos_gui_live_window_evidence_mdi_titlebar_css_present=true
- macos_gui_live_window_evidence_event_titlebar_click_events=0
- macos_gui_live_window_evidence_event_body_click_events=0
- macos_gui_live_window_evidence_window_found=false
- macos_gui_live_window_evidence_window_title=
- macos_gui_live_window_evidence_window_rect=
- macos_gui_live_window_evidence_capture_path=/private/tmp/macos-gui-live-evidence/simplegui-window.png
- macos_gui_live_window_evidence_capture_bytes=0
- macos_gui_live_window_evidence_capture_cksum=0
- macos_gui_live_window_evidence_capture_width=0
- macos_gui_live_window_evidence_capture_height=0
- macos_gui_live_window_evidence_capture_total_pixels=0
- macos_gui_live_window_evidence_non_background_pixels=0
- macos_gui_live_window_evidence_non_background_ratio=0.000000
- macos_gui_live_window_evidence_titlebar_css_pixels=0
- macos_gui_live_window_evidence_titlebar_widget_fill_pixels=0
- macos_gui_live_window_evidence_titlebar_widget_accent_pixels=0
- macos_gui_live_window_evidence_titlebar_widget_text_pixels=0
- macos_gui_live_window_evidence_completed_event_counter_pixels=0
- macos_gui_live_window_evidence_release_gate=live-macos-window-visual-proof
- macos_gui_live_window_evidence_release_gate_status=not-satisfied
- macos_gui_live_window_evidence_gui_smf_artifact_contract_status=missing
- macos_gui_live_window_evidence_gui_smf_artifact_contract_row=GUI_SMF_ARTIFACT_CONTRACT status=missing artifact=build/gui/pure_gui_hot.smf sha256= size=0 smf_role=-1 arch=0 embedded_dynlib=false symbol=gui_dynlib_hot_probe_tick qemu_status=not-run qemu_reason=live-qemu-not-executed macos_status=not-run macos_reason=requires-macos-arm64
- macos_gui_live_window_evidence_report_path=doc/09_report/macos_gui_live_window_evidence_2026-07-17.md

## GUI SMF Artifact Contract Output
- GUI_SMF_ARTIFACT_CONTRACT status=missing artifact=build/gui/pure_gui_hot.smf sha256= size=0 smf_role=-1 arch=0 embedded_dynlib=false symbol=gui_dynlib_hot_probe_tick qemu_status=not-run qemu_reason=live-qemu-not-executed macos_status=not-run macos_reason=requires-macos-arm64

## Shared MDI Titlebar Contract Output
- shared_mdi_titlebar_contract_status=pass
- shared_mdi_titlebar_contract_titlebar_button_markup_present=true
- shared_mdi_titlebar_contract_titlebar_input_markup_present=true
- shared_mdi_titlebar_contract_body_button_markup_present=true
- shared_mdi_titlebar_contract_body_input_markup_present=true
- shared_mdi_titlebar_contract_titlebar_css_present=true
