# Stage2 native-cache witness loses its receiver

Date: 2026-09-22. Baseline: `396934b0ec49fdb82d53e40cbd2ae8e23100f588`.
Status: native projection red/green PASS; independent Astra review PASS.
Actual rebuilt Stage2 admission and general method receiver transport remain open.

## Failure and exact causal evidence

The parent native build completed (3 compiled, 896 cached), then positional
hello-world admission failed with SIGSEGV/139 at `phase=native_cache`.
Candidate retained at:

`/Users/ormastes/simple-tmp/macos-bootstrap-restart-20260922/build/evidence/macos-enforced-bd544/stage2-borrow-396934b/simple.rejected`

SHA-256: `198774442fe47f5a1f65483d08120b4809a2e4952377bdb41dea2d0e8ab77495`.

Isolated evidence root:
`/Users/ormastes/simple-tmp/macos-native-cache-20260922/build/native_probe/native-cache`.

`crash.log` captures the exact candidate under LLDB using backend LLVM;
`cranelift.log` captures its witness-entry registers using the admission's
Cranelift backend. Both reach the shared cache path. The latter stops after
the expected failure to read address 0x40; it does not itself capture a second
SIGSEGV. Both diagnostics use isolated caches, `SIMPLE_BOOTSTRAP=0`,
`SIMPLE_NO_STUB_FALLBACK=1`, `SIMPLE_FRONTEND_DELEGATED=1`,
`SIMPLE_NATIVE_BUILD_FORCE_WORKER=0`, local `SIMPLE_LIB`, the retained LLVM23
environment, and the exact frozen runtime authority below. Argv matches
admission: `native-build --backend <backend> --runtime-bundle core-c-bootstrap
--entry-closure --cache-dir <isolated> --mode one-binary
scripts/check/cert/redeploy_gate/fixtures/hello_world.spl --output <isolated>`.
Diagnostic LLDB exit zero is not compiler success.

The failing symbol is
`compiler__driver__cache__native_module_witness__native_module_cache_witness_v1`
at **+616**, `ldr x27, [x14, #8]`, address **0x48**. Its dependency input is
**0x40**, the length of the MIR SHA-256 text. The stack proceeds through
`NativeModuleCacheFactSetV1_dot_witness+380` and
`driver_native_shadow_witness_v1+760`.

`shadow.disasm` proves that +736..756 marshals only `mir_identity` and `config`
for `complete_facts.witness(mir_identity, config)`. The required fact-set
receiver is omitted. `facts.disasm` then interprets the hash as its receiver:
module ID is a text header (`0x5800000001`), dependencies are length 64,
and layouts are hash bytes (`0x3439643631613438`). `witness.disasm` shows
the invalid dependency pointer passed to `rt_for_iterable` and dereferenced.

## Correction and scope

Call the existing `native_module_cache_witness_v1` directly with all six
arguments projected from `complete_facts`, MIR identity, and configuration.
The preceding `complete_facts.valid` guard remains authoritative, so bypassing
the method's duplicate guard preserves invalid-fact behavior. Witness hashing,
cache admission, and mismatch handling are unchanged.

This removes one method call and its receiver copy, without new allocation,
scan, cache, or fallback. It contains this bootstrap call site; it does not
repair general inferred native receiver lowering. The related prior report
is `stage2_borrow_check_stale_receiver_exit1_2026-09-22.md`. Existing malformed
HIR diagnostics are separately unresolved and were not suppressed.

## Native regression and resource evidence

Recipe: `test/fixtures/native/native_cache_receiver/README.md`.
The exact production call and real fact-set structure/method are extracted;
only the fact producer is modeled. Both variants import the real unchanged
witness implementation, encoders, and SHA-256 code. Support and scenarios are
identical across variants. This does not execute the entire driver.

Explicitly authorized bootstrap-only producer/runtime authority:
`/Users/ormastes/simple-tmp/macos-bootstrap-restart-20260922/build/bootstrap/macos-enforced-bd544-stage2/stage3/aarch64-apple-darwin/stage2-runtime-authority`.

- Producer `simple` SHA: `3ff20095e350af7f0b5cc150fd59872b073955eced1e10f3e264ca4a1e37c0a6`.
- Runtime `libsimple_native_all.a` SHA: `5e11731fa77990ecc170b939d2b16a48a1d9be417069202f365861e69576006d`.
- Red executable SHA: `2f91f3feba6f6a57212d7cce72d2c10d6189c17c582f6658d6ebf6d936b0b8cb`.
- Green executable SHA: `d247669e8e7e0bc8493e13ac1f1cd2bf4c7596201088812df35a1cf5e6d38d44`.
- Fixed owner SHA: `37c9040e1dd536ef11350b1302cf817d3a448519d240c3208dccaefa45a14330`.

Red exits **139**. Green exits **0**, prints `native-cache-receiver-pass`,
and verifies empty/nonempty dependencies, module/MIR identity, changed folds,
direct-construction agreement, missing module rejection, and malformed
dependency rejection. Nonempty resolution/layout arrays are not covered.
`red-call.disasm` repeats the omitted receiver at +184..204;
`green-call.disasm` loads the four real fields and passes six arguments.

| Measurement | Red | Green |
|---|---:|---:|
| Compiled / cached / failed | 14 / 0 / 0 | 14 / 0 / 0 |
| Build wall time, seconds | 2.75 | 2.55 |
| Build sampled process-tree peak, KiB | 205600 | 210240 |
| Build executable peak RSS, bytes | 156532736 | 156090368 |
| Run wall time, seconds | 0.35 | 0.34 |
| Run executable peak RSS, bytes | 8732672 | 9093120 |
| Run sampled process-tree peak, KiB | 2560 | 2576 |

All four build/run guards report zero observer errors and quiescent cleanup;
cap 5859375 KiB, build deadline 180 seconds, run deadline 20 seconds. The
LLDB diagnostic peak is 1947376 KiB and includes debugger overhead. Native
projection builds are below the ordinary decimal 1 GB target. Single short
runs and sampling establish bounds, not speedup or general performance;
sampling misses peaks visible to `/usr/bin/time -l`.

One production fix cycle; no bootstrap or full compiler build. General
compiler/library/MCP/LSP checks, SSpec, Stage2 admission, Stage3 eligibility,
deployment, and release PASS remain unavailable until an admitted compiler
exists. No seed-based general test result or push is claimed.

Independent Astra review verified the unchanged validity gate, exact call
arguments, extracted struct and scenarios, native disassembly, all six hashes,
and resource receipts. No blocking findings. Working/staged direct-env audits
and whitespace checks passed; `doc/06_spec` has zero executable `_spec.spl`
files. These are scoped commit checks, not production verification PASS.
