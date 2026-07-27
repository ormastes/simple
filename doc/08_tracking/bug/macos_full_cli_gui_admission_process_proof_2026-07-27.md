# macOS Full-CLI GUI Admission Process Proof

**Status:** fail-closed / review-cycle cap reached
**Evidence row:** `MAC-WM-GLASS-LOCAL-001`

The manifest-v3 candidate cannot admit a live GUI driver yet:

1. Its forbidden-process check rejects the canonical driver's own
   `build/bootstrap/full/<platform>/simple` path merely because it contains a
   `bootstrap` component.
2. The behavior probe self-reports its PID/path/hash and polls `ps` every
   50 ms. That cannot exclude a same-PID `exec` delegate after the first sample
   or a shorter-lived forbidden child between samples.

The launcher-side immutable hash binding is retained as useful source work, but
the producer/admission candidate must not be committed or used for live
evidence until both defects are repaired and independently accepted.

## Required repair

- Classify forbidden descendants by admitted executable identity/role, not a
  substring in the canonical root path.
- Replace polling/self-attestation with an OS-backed execution-history
  boundary that covers root executable identity and every descendant through
  exit, including same-PID `exec`.
- Add negative fixtures for same-PID `exec` delegation and a sub-50-ms
  seed/bootstrap child.
- Re-run these exact focused admission contracts in a fresh scoped session,
  then request highest-capability review:

  ```sh
  sh test/01_unit/scripts/macos_gpu_trusted_build_admission_contract.shs
  sh test/01_unit/scripts/macos_gui_full_cli_provenance_contract.shs
  sh -n scripts/check/build-macos-full-cli-gui-provenance.shs
  sh -n scripts/check/lib/macos-gpu-trusted-build-admission.shs
  sh -n scripts/gui/macos-gui-run.shs
  ```

  Do not bootstrap or substitute the Rust seed.

After acceptance, produce the canonical full CLI and manifest, then run:

```sh
sh scripts/check/check-macos-vulkan-gui-widget-live-evidence.shs
sh scripts/check/check-macos-vulkan-web-live-evidence.shs
```
