# Item 5 Stage4 explicit link-input admission

Status: focused native PASS; full Stage4 qualification OPEN.

The strict LLVM Stage4 link path profiles selected runtime archives before it applies `NativeLinkOptions`. Caller `libraries`, `library_paths`, and `linker_flags` were previously forwarded after that profile, so they could change the final link without appearing in the exact closure receipt. `SIMPLE_LINK_OBJECTS` was already rejected.

The Stage4 orchestrator now rejects all three caller input families before runtime compilation or archive projection. Ordinary links retain explicit input forwarding. The pure guard lives in `src/compiler/70.backend/backend/llvm_stage4_explicit_link_inputs.spl`; `test/01_unit/compiler/backend/llvm_explicit_link_options_spec.spl` includes assertions for each family.

The admitted pure-Simple Stage 2 compiler (SHA-256 `e0e5a6cd522d6ee86b0dbb8e7cdd88cad21b3daa39d18b65b2ce163867e0eb06`) compiled the one-module guard to SMF with `SIMPLE_NO_STUB_FALLBACK=1`. A no-stub `native-build --entry-closure --backend cranelift --runtime-bundle core-c-bootstrap` of `test/01_unit/compiler/backend/stage4_explicit_guard_native_probe.spl` linked two objects and its executable exited 0. Logs: `build/mini_builds/item5_stage4_explicit_pure_guard_20261011.log` and `build/mini_builds/item5_stage4_explicit_guard_native_probe_scoped_20261011.log`. The binary is `build/mini_builds/item5_stage4_explicit_guard_native_probe_20261011` (29,792 bytes); this is a probe size, not a hello size gate.

A direct 544-module compile of the hosted support owner timed out at 120 seconds during HIR 125/544, with no source diagnostic. The full Stage4 CLI, exact `RuntimeFeatureClosureV1`, optional provider demand loading, matched C hello size, startup/RSS cohorts, and cross-platform parity remain unverified.
