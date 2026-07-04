# macOS GUI Live Window Evidence

- GUI SMF artifact contract status: missing
- GUI SMF artifact contract row: GUI_SMF_ARTIFACT_CONTRACT status=missing artifact=build/gui/pure_gui_hot.smf sha256= size=0 smf_role=-1 arch=0 embedded_dynlib=false symbol=gui_dynlib_hot_probe_tick qemu_status=not-run qemu_reason=live-qemu-not-executed macos_status=not-run macos_reason=requires-macos-arm64
- GUI SMF artifact contract scope: contract-only; does not promote live macOS window evidence

## Raw Evidence

- macos_gui_live_window_evidence_status=pass
- macos_gui_live_window_evidence_reason=pass
- macos_gui_live_window_evidence_host_os=macos
- macos_gui_live_window_evidence_launcher=macos-gui-run
- macos_gui_live_window_evidence_window_found=true
- macos_gui_live_window_evidence_window_title=SimpleGui
- macos_gui_live_window_evidence_window_rect=200,120,640,512
- macos_gui_live_window_evidence_capture_path=build/tmp/macos_gui_live_window_evidence/simplegui-window.png
- macos_gui_live_window_evidence_capture_bytes=54083
- macos_gui_live_window_evidence_capture_cksum=355617546
- macos_gui_live_window_evidence_capture_width=1280
- macos_gui_live_window_evidence_capture_height=1024
- macos_gui_live_window_evidence_capture_total_pixels=1310720
- macos_gui_live_window_evidence_non_background_pixels=1310426
- macos_gui_live_window_evidence_non_background_ratio=0.999775
- macos_gui_live_window_evidence_release_gate=live-macos-window-visual-proof
- macos_gui_live_window_evidence_release_gate_status=satisfied
- macos_gui_live_window_evidence_gui_smf_artifact_contract_status=missing
- macos_gui_live_window_evidence_gui_smf_artifact_contract_row=GUI_SMF_ARTIFACT_CONTRACT status=missing artifact=build/gui/pure_gui_hot.smf sha256= size=0 smf_role=-1 arch=0 embedded_dynlib=false symbol=gui_dynlib_hot_probe_tick qemu_status=not-run qemu_reason=live-qemu-not-executed macos_status=not-run macos_reason=requires-macos-arm64
- macos_gui_live_window_evidence_report_path=doc/09_report/macos_gui_live_window_evidence_2026-06-09.md

## GUI SMF Artifact Contract Output
- GUI_SMF_ARTIFACT_CONTRACT status=missing artifact=build/gui/pure_gui_hot.smf sha256= size=0 smf_role=-1 arch=0 embedded_dynlib=false symbol=gui_dynlib_hot_probe_tick qemu_status=not-run qemu_reason=live-qemu-not-executed macos_status=not-run macos_reason=requires-macos-arm64
