# GUI/Web/2D Platform Evidence Bundle

- Status: fail
- Reason: invalid-live-gate-evidence
- Proven gates: 0
- Missing gates: 9
- Failed gates: 1
- Stale gates (older than 72h): 
- Invalid (corrupt/truncated) gate evidence: production-gui-web-parity
- Remaining gates: linux-vulkan-renderdoc|macos-metal-xcode-gpu-capture|windows-d3d12-pix|windows-electron-vulkan-parity|ios-tauri-wkwebview-metal|android-tauri-webview-vulkan|retained-4k-8k-current-source|full-html-css|cross-platform-freshness|production-gui-web-parity

This checker is non-launching. It consumes env files from the platform
render-log, mobile, retained performance, HTML/CSS, production parity, and
freshness checkers. Missing evidence remains incomplete; failed evidence
remains failed. Upstream env files must contain their expected keys
(otherwise: invalid) and be newer than MAX_EVIDENCE_AGE_HOURS=72h
(otherwise: stale); both are treated as failures, never as proof.
