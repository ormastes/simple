# Windows receiver gate output suffix and failure evidence

## Defect

The canonical Stage2 receiver gate requested an extensionless executable. The retained Windows compiler returned zero but emitted the same basename with `.exe`; the requested path was absent. The gate must request the platform filename consistently for both its receiver probe and positional Stage3-route probe. Linux and macOS continue to use extensionless paths.

The previous `if ! compiler` branch discarded the actual compiler exit code, reported a receiver capability failure before receiver execution, and removed the failed probe directory. The fix preserves and reports compile status, retains failed probes, and supports `STAGE2_RECEIVER_KEEP_PROBE_DIR=1` for retaining successful diagnostic evidence. Executable paths are quoted.

## Measured regression evidence

Frozen source: `403a5409fbc65aef59f4f23dd8edd7a465ea721f`.
Retained Phase2 producer SHA256: `83a7f5f163c27308c8d2c35748dac75af0f210dcd62f51998ff2e8d5f6493668`.

One bounded three-case cohort observed compile exit zero in every case. Explicit-entry `.exe` and positional `.exe` artifacts both executed the actual receiver fixture with exact expected stdout. The extensionless case emitted `.exe` and was not executed because the requested filename was absent. Evidence: `D:/dev/simple-windows-receiver-diagnostic-20260929/83a7f5f163c2-cohort1`.

One subsequent invocation of the actual patched canonical gate against the unchanged producer and runtime passed both real criteria:

- `bootstrap_stage2_struct_receiver=PASS`
- `bootstrap_stage2_positional_stage3_route=PASS`

Guardian and native exit statuses were zero, before/after input hashes matched, and both executable artifacts were retained. Evidence: `D:/dev/simple-windows-receiver-diagnostic-20260929/83a7f5f163c2-fixed-gate1/result.json`; SHA256 `4a778d4389c62f4e015b9aac96c1dddf89c06d1174b38a810c500182e922cc08`. These observations are a focused regression check, not admission or broad bootstrap qualification.

## Remaining limits

The original canonical run failed its compile-command branch. That nonzero status was not reproduced by the cohort, and the filename mismatch does not explain it. The old failure remains preserved. Dedicated source-level orchestration regression coverage is prepared separately with the shared bootstrap regression helper; it has not been run and is not claimed as passing by this fix. Negative compile-status propagation has static review only in this patch.

## Release-specific adaptation limits (historical)

The Release832b snapshot had only the mutable-receiver probe in this gate. Its adapted fix applied to that execution boundary and preserved the original arguments and runtime defaults. Explicit strict-stub and Windows ABI/linker selection were separately imported prerequisites from the reviewed main gate. The positional Stage3 route probe described above was absent from that release snapshot, so its suffix and quoting changes were not part of the release adaptation. Bringing that route coverage to release requires a separate reviewed prerequisite. The adaptation claimed no exact patch-ID backport, target runtime PASS or release admission.
