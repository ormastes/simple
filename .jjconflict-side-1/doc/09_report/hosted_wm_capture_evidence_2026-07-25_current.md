# Hosted WM Capture Evidence

- status: diagnostic-pass
- production_admission: fail
- reason: runtime-seed-missing-manifest-and-local-raster-fallback
- simple_bin: bin/release/aarch64-apple-darwin-macho/simple
- simple_bin_source: repo-self-hosted-fallback
- simple_bin_status: pass
- capture_ppm: build/wm-glass-theme-host-current/hosted_wm_first_frame.ppm
- width: 16
- height: 16
- non_background_pixels: 90
- bright_pixels: 66
- accent_pixels: 190
- sample_checksum: 473142143
- theme_id: aetheric_dark
- theme_source_manifest_sha256:
- render_us: 0
- backend_selected: simple_web_request_local_raster_readback
- backend_fallback_reason: Metal submit/readback is not wired; local WebRenderRequest pixels were used
- backend_readback_status: verified:webrender-request-local-pixels
- event_evidence: absent
- launcher_log: build/wm-glass-theme-host-current/capture.log

This retained 16x16 image validates only the diagnostic pixel writer. It is
not production host evidence because the selected launcher emitted the Rust
bootstrap-seed warning, package source provenance is empty, the native
submit/readback path fell back to local pixels, and no event/performance
sequence is bound to this frame.
