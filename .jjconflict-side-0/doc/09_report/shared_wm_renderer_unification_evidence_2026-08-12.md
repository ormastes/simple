# Shared WM Renderer Unification Evidence

- status: unavailable
- reason: simple-bin-forbidden
- simple_bin: bin/simple
- simple_bin_source: explicit-env-rust-seed-forbidden
- simple_bin_status: forbidden
- source_revision: 08424ed7075de28df64fadb50a541cafd82a4366
- classification: current-host-executable
- blocker: admitted self-hosted Simple binary required; selected binary identifies as Rust bootstrap seed
- resume_command: SIMPLE_BIN=<admitted-self-hosted> sh scripts/check/check-shared-wm-renderer-unification-evidence.shs
- evidence_scope: host-side shared lifecycle/source contract only; no GPU/QEMU execution
