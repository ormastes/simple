# Windows Stage3 coordinator rejects its own policy handoff on exact 8b131cb

Status: OPEN (P1). No Stage3 executable was produced by the coordinator lane.

## Authority and symptom

The Windows Stage2 compiler at `D:/b8bfresh/build/bootstrap8b/stage3/x86_64-pc-windows-msvc/stage2-admitted/simple.exe` is admitted for source revision `8b131cbf1c64ebf9034700e4369a015777b35f45`; its SHA-256 is `bee5699df10d7ba1e54263e18c6f81a5b2c5165909711e83ecf4810cbe675c25`. The exact-source speculative Stage3 launch had a valid Stage2 admission and planner receipt, then exited 1 before source loading:

```text
error: native-build could not create its internal policy handoff: invalid-internal-argument:corrupt
```

Retained evidence: `D:/b8bfresh/build/native_probe/stage3-speculative8b/build.log` and `terminal.env`. This remains quarantined diagnostic evidence, not a Stage3 admission.

## Narrowed path

`bootstrap_main.spl` selects `run_bootstrap_stage3_process_route` only when the requested route is not `direct` and the parsed thread count exceeds 1. That function calls `run_native_build_worker`, which prepares a policy, encodes it, and immediately passes the encoded text to `environment_variant_policy_handoff_attach_v1`. The attach function decodes the text before adding it to worker argv. The error above is the decoder's `Corrupt` result at this parent-side attach check; no worker child or compiler source load is required to reproduce it.

The decoder has exactly three `Corrupt` exits: (1) strict Base64url decode failure, (2) malformed 64-hex-character policy/cache/integrity digest, or (3) canonical recomputation mismatch. The current error does **not** distinguish them. Encoding already verified the original handoff against a newly constructed canonical value; the failure appears only after encoding and decoding, but that does not prove a codec defect.

Fast preflight probes with a deliberately absent `.spl` entry used the same admitted compiler and isolated caches. `--threads 2`, `10`, `11`, `12`, and `--threads=12` all returned `invalid-internal-argument:corrupt`. `--threads 1` and `--threads 01` took the direct route and reached the expected `collected zero source files` error. A valid `SIMPLE_PARSER_PREFER=scalar` source did not change the coordinator result. These comparisons localize the defect to the coordinator handoff path, rather than the digit count of the thread argument. Logs are under `D:/b8bfresh/build/native_probe/{preflight-*,arg-*,policy-*}.log`.

An interpreter bootstrap diagnostic of `D:/b8bfresh/build/native_probe/stage3-policy-probe.spl` returned `small=true`, `encoded_len=1884`, `decode=ok`. It proves source-level roundtrip for that snapshot, not native correctness. A candidate-native 35-module probe spent over 600 CPU seconds at HIR module 1/35 with no object and was stopped. A smaller 8-module Base64-only native probe segfaulted after unresolved method calls (`new`, `bytes`, `splat`, `to_array`) were lowered to const-0 placeholders despite `SIMPLE_NO_STUB_FALLBACK=1`; see `D:/b8bfresh/build/native_probe/stage3-base64-probe.log`. Neither probe yielded a native executable, so the exact `Corrupt` exit is still unproven.

## Next falsifiable fix gate

Instrument the three decoder `Corrupt` exits with distinct typed reasons in a fresh compiler source revision, retain strict rejection, and run one focused native policy roundtrip before rebuilding Stage2. Do not suppress attach validation or treat a parent-side failure as worker success. A new Stage2 candidate must prove that the same `--threads 12` coordinator preflight reaches source loading, then pass canonical Stage3 admission and Phase2 qualification separately.

`SIMPLE_BOOTSTRAP_STAGE3_REQUESTED_ROUTE=direct` is an explicit diagnostic route and may let a separate, planner-bound Stage3 attempt reach the compiler. The canonical resume script records `coordinator` whenever threads >1. Direct mode with `SIMPLE_NATIVE_BUILD_THREADS=12` resolves that request but currently prints `concurrency=1` in the driver, so it does not prove 12 parallel build jobs or canonical coordinator success.
