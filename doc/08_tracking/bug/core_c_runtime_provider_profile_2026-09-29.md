# Pure-Simple core-C runtime provider composition (2026-09-29)

## Failure and cause

Frozen candidate `61c95134bd4c3e57d9e046b85aca6ca99ec1e953` compiled the Linux full CLI but exceeded the process-group RSS cap during its Rust-owned link. One retained-object LLD diagnostic failed early on missing providers; it does not prove that a complete CLI link meets the memory cap.

A separate admitted Stage2 positional AOT probe selected `core-c-bootstrap`. The pure-Simple orchestrator suppressed Rust native-all but compiled its ordinary C list, which omitted the narrow portable core owners. All four Linux CPU, clock, and text/byte-array externs were unresolved. The source and object arrays also had different orders, assigning some compiled sources the wrong object and cache names.

## Correction

The orchestrator passes its selected bundle explicitly. The named core-C composition excludes the colliding `runtime.c` monolith, selects the portable C owner set and existing media/device providers, and derives object paths from those sources. Core-C aliases share a closed cache profile; cache version 5 includes the selected source order and owner flags. Ordinary and Stage4 source compositions retain their separate policies.

Windows symbol inspection found five progress-clock/TLS exports in both `runtime_native.c` and `runtime_timestamp.c`. The named profile elects the timestamp owner and suppresses only the native fallback block. Other profiles retain the fallback.

Removing the monolith also removed required LLVM helper exports. An unchanged shared private header now supplies the nine intrinsic ABI functions and integer power function through `runtime.c` for ordinary builds or `runtime_core_intrinsics.c` for the named profile. Bounds failures still terminate; memory operations and integer power retain their existing behavior.

## Evidence and limits

- Linux initial C census: 39 translation units compiled, 2,933 strong symbols, zero strong duplicates; four probe APIs had unique narrow C owners.
- Windows initial census: 37 units compiled; the five real timestamp duplicates were identified. Targeted timestamp correction passed with the other 36 objects reused.
- Windows incremental intrinsic census: the retained new object supplies all ten helpers uniquely; 37 prior objects were reused and no non-coalescible duplicates remain. The wrapper metadata exception occurred after compilation; its raw compiler exit was not persisted, so this evidence does not claim a recorded compiler exit of zero.
- Linux manual semantic cycle 1 resolved the four APIs but failed on the omitted bounds-check helper.
- Linux manual semantic cycle 2 rebuilt only the changed native provider and new intrinsic provider, reused 38 C objects, linked strictly, and executed the retained Stage2 probe: `COREC_PROVIDER_PASS`, exit 0.

Separate authorized old-61 diagnostics also stopped before compilation: positional full CLI resolved a 2,445-file closure and rejected the relative import `...monomorphize.note_sdn`; canonical Stage3 refused its fixed 48 GiB headroom requirement on a WSL VM with approximately 31 GiB total RAM. These failures are preserved without bypasses.

These are diagnostic C composition results, not production compiler admission. The focused profile/object-path specification, the new compiler's canonical full CLI/test-runner matrices, and Stage3/4 execution remain pending. The separate Windows probe entry-name defect is outside this runtime patch.

Diagnostic artifacts are preserved under the D-backed ext4 paths `corec-owner-census-68c39832-20260929` and `corec-owner-semantic-cycle{1,2}-20260929`, with Windows census evidence under `D:/dev/simple-windows-reviewed-bootstrap-20260929`.
