# macOS GUI Live Window Evidence

- GUI SMF artifact contract status: missing
- GUI SMF artifact contract row: GUI_SMF_ARTIFACT_CONTRACT status=missing artifact=build/gui/pure_gui_hot.smf sha256= size=0 smf_role=-1 arch=0 embedded_dynlib=false symbol=gui_dynlib_hot_probe_tick qemu_status=not-run qemu_reason=live-qemu-not-executed macos_status=not-run macos_reason=requires-macos-arm64
- GUI SMF artifact contract scope: contract-only; does not promote live macOS window evidence
- Shared MDI titlebar contract status: pass
- Shared MDI titlebar sample: src/app/ui_shared_mdi/main.spl

## Raw Evidence

- macos_gui_live_window_evidence_status=skip
- macos_gui_live_window_evidence_reason=requires-macos
- macos_gui_live_window_evidence_host_os=linux
- macos_gui_live_window_evidence_launcher=macos-gui-run
- macos_gui_live_window_evidence_sample=src/app/ui_shared_mdi/main.spl
- macos_gui_live_window_evidence_mdi_titlebar_contract_status=pass
- macos_gui_live_window_evidence_mdi_titlebar_button_markup_present=true
- macos_gui_live_window_evidence_mdi_titlebar_input_markup_present=true
- macos_gui_live_window_evidence_mdi_body_button_markup_present=true
- macos_gui_live_window_evidence_mdi_body_input_markup_present=true
- macos_gui_live_window_evidence_mdi_titlebar_css_present=true
- macos_gui_live_window_evidence_window_found=false
- macos_gui_live_window_evidence_window_title=
- macos_gui_live_window_evidence_window_rect=
- macos_gui_live_window_evidence_capture_path=
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
- macos_gui_live_window_evidence_release_gate=live-macos-window-visual-proof
- macos_gui_live_window_evidence_release_gate_status=not-satisfied
- macos_gui_live_window_evidence_gui_smf_artifact_contract_status=missing
- macos_gui_live_window_evidence_gui_smf_artifact_contract_row=GUI_SMF_ARTIFACT_CONTRACT status=missing artifact=build/gui/pure_gui_hot.smf sha256= size=0 smf_role=-1 arch=0 embedded_dynlib=false symbol=gui_dynlib_hot_probe_tick qemu_status=not-run qemu_reason=live-qemu-not-executed macos_status=not-run macos_reason=requires-macos-arm64
- macos_gui_live_window_evidence_report_path=doc/09_report/macos_gui_live_window_evidence_2026-06-14.md

## GUI SMF Artifact Contract Output
- GUI_SMF_ARTIFACT_CONTRACT status=missing artifact=build/gui/pure_gui_hot.smf sha256= size=0 smf_role=-1 arch=0 embedded_dynlib=false symbol=gui_dynlib_hot_probe_tick qemu_status=not-run qemu_reason=live-qemu-not-executed macos_status=not-run macos_reason=requires-macos-arm64

## Shared MDI Titlebar Contract Output
- [33mwarning[0m: Deprecated syntax for type parameters
-   --> /tmp/simple-mdi-linux-plan/src/lib/common/ui/style.spl:559:64
-    |
- 559 |         while j >= 0 and current.selector.specificity < matched[j].selector.specificity:
-    |                                                                ^
- 
- Use angle brackets: matched<...> instead of matched[...]
- 
- Run `simple migrate --fix-generics` to automatically update your code
- 
- shared_mdi_titlebar_contract_status=pass
- shared_mdi_titlebar_contract_titlebar_button_markup_present=true
- shared_mdi_titlebar_contract_titlebar_input_markup_present=true
- shared_mdi_titlebar_contract_body_button_markup_present=true
- shared_mdi_titlebar_contract_body_input_markup_present=true
- shared_mdi_titlebar_contract_titlebar_css_present=true
