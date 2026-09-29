# Simple web server strict native admission — 2026-08-12

## Identity

- Compiler: `build/simpleos-enhance-current-stage2/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple`
- Compiler SHA-256: `84e60ed802e6fe49c7df015ff87fd58ac7fa40253c1e1833bc72757d59462c50`
- Gate: `scripts/check/build-simple-web-server-native.shs`
- Backend/host: Cranelift, `x86_64-unknown-linux-gnu`
- Strict mode: `SIMPLE_NO_STUB_FALLBACK=1`
- Output/cache: `build/native_probe/web-admitted-20260812/`

## Attempts

1. Initial gate: **FAIL**, exit 1, 46.36 s, 1,166,124 KiB maximum RSS.
   Native codegen rejected three invalid nested/module loads: out-of-scope
   `damage_enabled`, module alias `variables`, and receiver `self` inside a Dict
   literal. No artifact was admitted.
2. One permitted corrective gate: **FAIL**, exit 1, 1:57.35, 1,242,328 KiB
   maximum RSS. The three body failures were eliminated and compilation reached
   the final linker. Linking then rejected 166 references covering 101 unique
   runtime symbols; the first was `text_dot_from_char_code`, with further hosted
   GPU Vulkan/Metal runtime exports among the failures. No artifact was emitted.

## Result

**STATUS: FAIL.** The strict native web artifact, `--check`, hash, and loopback
SSR smoke remain unavailable. This is not live-server or performance evidence.
Per the bounded two-attempt policy, no third build was run. Retained evidence:
`gate.stdout`, `gate.stderr`, `gate-corrective.stdout`,
`gate-corrective.stderr`, `build.log`, `resource.txt`, and
`resource-corrective.txt` under the output directory above.

## New admitted compiler / host-GPU authority probe

A later, independently admitted pure-Simple compiler was exercised exactly once
with a fresh cache through the canonical strict wrapper:

- compiler: `/mnt/data/bs2/fixverify/build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple`
- compiler SHA-256: `dfd3c3b7d807384d5531e744df06018a2158622d0c3181c2b09b5c6a8cc54ed6`
- host-GPU runtime: `build/simpleos_gpu_host/x86_64-vulkan-cuda-runtime-target/bootstrap/libsimple_runtime.a`
- runtime SHA-256: `93dee95e2fd30f8ad1dde63b7c4728b7ca6644a4fbc384d10819304dff9ffd3f`
- evidence/cache: `build/native_probe/web-dfd3-hostgpu-tls-20260812/`

The source-level hosted TLS provider self-check passed before the build. The
strict build then reached the final linker and failed after 1:37.39 with
1,148,340 KiB maximum RSS. The pinned host-GPU archive does not define
`rt_byte_char`, `rt_rsa_decrypt`, `rt_wire_to_hex`, `rt_hex_to_wire`, or
`rt_random_i64`; `nm` confirmed all five absent and the linker rejected exactly
those provider references. No executable exists, so `--check`, artifact hash,
HTTP/1 `/render` PNG loopback, and concurrent-request evidence were not run.
No retry or second full build was performed.

**STATUS: FAIL — runtime/provider authority mismatch.** Retained evidence is
`authority.sha256`, `source-gate.sha256`, `git-head.txt`,
`git-status-before.txt`, `gate.stdout`, `gate.stderr`, `build.log`, the isolated
cache, and retained native objects in that evidence directory.

## Rebuilt host-GPU capsule retry

The newer host-GPU archive and its separately admitted hosted-TLS supplement
were exercised once through the canonical strict wrapper with a fresh cache:

- compiler SHA-256: `dfd3c3b7d807384d5531e744df06018a2158622d0c3181c2b09b5c6a8cc54ed6`
- host-GPU archive SHA-256: `9b81a138ffdb031f73fc25f6343fcadd06c76ab9650d2e5df835673b77c9bd35`
- hosted-TLS object SHA-256: `2f8e02cfc2a92c3e516c152a8f48a199a4910d124087e8545e044eda305bd4ce`
- evidence/cache: `build/native_probe/web-dfd3-hostgpu-tls-rebuilt-20260812/`

The focused hosted-TLS ABI/provider gate passed. The strict native build then
reached the final linker and failed after 1:34.39 with 1,025,456 KiB maximum
RSS. The emitted link command did not consume the separately admitted TLS
supplement and rejected exactly `rt_byte_char`, `rt_rsa_decrypt`,
`rt_wire_to_hex`, `rt_hex_to_wire`, and `rt_random_i64`. The retained host-GPU
archive deliberately does not own those symbols; the manifest assigns them to
`runtime_tls_hosted.o`. No executable exists, so `--check`, artifact hashing,
PNG/IHDR loopback, and concurrent unrelated-request progress were not run. Per
the requested bounded procedure, there was no corrective rebuild.

**STATUS: FAIL — the admitted compiler's host-GPU link path does not attach the
admitted hosted-TLS supplement.** This is native linker admission evidence, not
live-server or performance evidence.
