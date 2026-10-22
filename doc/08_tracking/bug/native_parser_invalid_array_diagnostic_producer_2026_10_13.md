# Native parser invalid-array diagnostic producer

Status: observed compiler runtime diagnostic; private diagnostic executable linked but **not executed**. No production repair or performance improvement is qualified. Bug database reconciliation is pending.

## Observed failure

The retained original renderdoc-metrics compilation reported `rejected invalid array handle before dereference` with value `0x0000028b19de54a1`, between the progress markers for parsing `lib.nogc_sync_mut.sffi.cli_args.spl` at 541–553 ms. It continued and produced an archive. Exit zero and archive presence therefore do not establish compiler correctness.

The original worker log is `C:/p3/build/native_probe/phase4-renderdoc-metrics-native-20261013-astra/receiver-attempt1/worker.log`, SHA-256 `4410d3c02dadbf554ffb8edef560a7bbecbfb501db0c019ca8d13ac8903c1fd5`. It contains no stack identifying the caller. The runtime reports this rejection only once per process; one message does not prove one invalid access. The exact cause, including any parser ownership or ABI defect, remains unresolved. The private TLDR integration was not applied to this producer.

## Diagnostic preparation and actual result

The private patch adds environment-gated capture of at most 32 return addresses after the existing invalid-array refusal. It does not dereference the rejected pointer, disable the guard, or change the valid-array path. Only `runtime_native.c` was recompiled; the other 37 runtime objects and the retained 1,314-member compiler archive were reused. The original worker and runtime archive remain preserved.

The bounded three-attempt build criterion is closed:

1. The collector rejected an incorrectly scoped storage path before compilation.
2. Preprocessing, C compilation and archive creation succeeded. A diagnostic archive observer then rejected valid Microsoft NUL-terminated long names because it expected newline termination.
3. The corrected observer verified all 38 ordered runtime member names, sizes and payload hashes against pinned inputs and an independent `llvm-ar` listing. A link-only continuation reused the completed C object/archive and produced the diagnostic executable. It did not rerun compilation.

The final link exited zero, reported final Job membership zero, and retained unchanged input pins. Its map records the real compiler entry, module initializer dispatcher and runtime entry points. These are link checks, not native parser tests.

Evidence root: `build/native_probe/invalid-array-parser-trace-20261013-astra/`.

| Artifact | SHA-256 |
|---|---|
| `DIAGNOSTIC_ONLY.patch` | `bebc7323af31500c0b5913a421e0a056d6f62e61cafb7d06426784017aa03a33` |
| `producer-link3/RESULT.json` | `6c31a2cfe40a5013a54f62aaa7d83ce176843065c2996827a2d2eff7dcf1483f` |
| `producer-link3/attempt/receipt.env` | `e5120cb5144a61a0eb124e54bd23e79c2bc35a391c70dc8b57e901d570af9a13` |
| `producer-link3/diagnostic-worker.exe` | `63544ef0aaec48c9ed2620f578b535f1f44864cf6070f39d35de9318be91a4c6` |
| `producer-link3/diagnostic-worker.map` | `4803f5407018cb5467db40eccd11adea44c80750d0ca03124a2af65096cf6bad` |

## Remaining qualification

A tiny committed project retains the original `cli_args.spl` bytes and a caller entry. Canonical source-authority preparation and execution of the diagnostic worker are **UNRUN** at this report's cutoff. They require separately reviewed requests. Captured addresses, if obtained, must be correlated with this exact executable/map and inspected before naming the faulty caller. Parser ownership regressions, memory safety, cold/warm latency and the 0.1-second target remain unqualified. This report publishes evidence only; no diagnostic runtime code or private optimization patch is promoted.
