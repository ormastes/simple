# X25519MLKEM768 Vulkan SPIR-V artifact — RESOLVED (physical evidence, both devices, full stage sweep)

Date: 2026-08-05
Worktree: `/home/ormastes/dev/pub/simple/.claude/worktrees/x25519-paired-timing`
Campaign: `.spipe/x25519mlkem768_acceleration/state.md`, AC-5 (Vulkan lane)

## Summary

T-02 reported Vulkan as BLOCKED: no
`build/evidence/x25519mlkem768/vulkan/x25519mlkem768_ntt_{forward,inverse}.spv`,
no `.comp` source, no generator, in this worktree — and could not find the
previously-tracked barrier-mismatch bug doc here either. Both readings were
correct for this worktree's disk state at the time.

Following the same pattern the sibling CUDA lane found (see
`x25519mlkem768_cuda_kernel_artifact_missing_2026-08-05.md`), the real
generator pipeline exists uncommitted in a different worktree,
`/home/ormastes/dev/pub/simple/build/worktrees/simpleos-engine2d-stage4-snapshot/`
(confirmed `git status --porcelain` shows every relevant path there as `??`,
never committed on any branch):

- `src/os/crypto/x25519_mlkem768/kernels/ml_kem_ntt_forward.comp` /
  `ml_kem_ntt_inverse.comp` — the GLSL compute-shader sources.
- `scripts/check/check-x25519mlkem768-vulkan-ntt.shs` — compile + validate +
  physical-probe-sweep + admit script.
- `doc/08_tracking/bug/x25519mlkem768_vulkan_ntt_barrier_mismatch_2026-08-02.md`
  — the historical bug doc T-02 could not find (it genuinely isn't in this
  worktree; it lives only in the snapshot worktree above).

**Action taken:** copied the `.comp` sources and check script into this
worktree (not committed, per task instructions) and regenerated the SPIR-V
fresh — not copied as a binary blob — using `glslangValidator` 15.1.0
(extracted from a cached `.deb` at `/tmp/simple_glslang/`, since no
system-wide GLSL→SPIR-V compiler is installed and `sudo` requires a password
this session has no way to supply) plus the system `spirv-val`.

## What was verified (re-derived independently, not trusted from secondhand hashes)

- `src/os/crypto/x25519_mlkem768/vulkan_ntt_provider.spl` (read in full):
  expects `build/evidence/x25519mlkem768/vulkan/x25519mlkem768_ntt_forward.spv`
  / `..._inverse.spv`, entry point `"main"`
  (`X25519_MLKEM768_VULKAN_NTT_ENTRY`), and validates via SHA-256 pin +
  SPIR-V magic (`0x07230203` little-endian) before admitting bytes into
  `CryptoVulkanSession.init`.
- `test/02_integration/os/crypto/x25519mlkem768_vulkan_candidate_spec.spl`
  hardcodes the constructor call with pinned digests
  `0865f588f0825a3ff66a1d5e2cd2a9d0c356bb75b4fceaaf5c2196ffa05f6379` (forward)
  and `07a11b541ef204a4fb6c907338dafc99bdf870d2046edcfad02a3d42dcca2687`
  (inverse) — matches T-02's report exactly. The spec has a **three-way
  branch**: (1) `admission_reason != ""` → asserts the error equals
  `"pinned-set-a-vulkan-keygen:" + executor.admission_reason` — this is
  **self-referential** (it reads the reason back off the executor), so it
  passes trivially for *any* admission failure, including a plain "file
  missing" or a digest mismatch from a wrong artifact. That branch must never
  be read as a real device pass. (2) `elif not vulkan_sffi_is_available()` →
  another self-consistent non-device branch. (3) `else` → the real path,
  asserting `outputs.compiled/submitted/fence_completed/device_readback` all
  `true`, `outputs.artifact_digest` equals the fixed literal
  `13ef51351c0147cf5fc71877d4eaac6730796e6833d78b49126e3159936d11e6`,
  `outputs.kernel_invocations` equals `7`, and
  `outputs.candidate_oracle_match` is `true`. Only branch 3 is real evidence.
- Confirmed which branch actually ran (rather than assuming): a throwaway
  probe spec asserting `vulkan_sffi_is_available().to_equal(true)` under the
  same interpreter harness failed with `expected 1 to equal true` — i.e. the
  underlying call returned a truthy `1` (available), just not the literal
  bool `true` the matcher wanted. This confirms Vulkan reports **available**
  in-harness, so with exact-matching pinned digests the spec cannot be taking
  branches 1 or 2. (Probe file created and deleted; not left in the tree.)

## Toolchain state on this host

- No `glslc`/`glslangValidator` installed system-wide; `apt-cache search`
  shows only `libshaderc1`/`libshaderc-dev` (library, not the CLI), and
  `sudo -n true` fails (`a password is required`) so `apt install
  glslang-tools` could not be run this session.
- A working `glslangValidator` (Glslang Version 11:15.1.0, matching the
  version string recorded in the 2026-08-02/03 bug-doc trail) was already
  present, pre-extracted from a cached `.deb`, at
  `/tmp/simple_glslang/usr/bin/glslangValidator` — leftover sandbox state
  from an earlier session on this host, not something this session installed.
- `spirv-val`/`spirv-dis` (package `spirv-tools`) are installed system-wide.
- `vulkaninfo --summary` (no `DISPLAY`) enumerates a working Vulkan 1.3.275
  instance; `lspci` shows two physical discrete NVIDIA GPUs (`RTX A6000`,
  `TITAN RTX`), matching the two devices the historical bug doc and T-02's
  report both reference.

## Regeneration and physical verification

Compiling the **unmodified** original `.comp` sources from the snapshot
worktree with `glslangValidator --target-env vulkan1.1` reproduces the pinned
SHA-256 hashes bit-for-bit:

```
$ sha256sum original_forward.spv original_inverse.spv
0865f588f0825a3ff66a1d5e2cd2a9d0c356bb75b4fceaaf5c2196ffa05f6379  original_forward.spv
07a11b541ef204a4fb6c907338dafc99bdf870d2046edcfad02a3d42dcca2687  original_inverse.spv
```

Running the copied-in official check script fresh on this host (own toolchain
lookup, own compile, own `spirv-val`, own physical probe sweep, own admission
copy — nothing pre-staged):

```
$ GLSLANG_VALIDATOR=/tmp/simple_glslang/usr/bin/glslangValidator \
    sh scripts/check/check-x25519mlkem768-vulkan-ntt.shs
```

produced **28/28 PASS** lines (stages 1 through 7, forward and inverse, both
physical devices), e.g.:

```
PASS backend=vulkan operation=forward device=0 name=NVIDIA TITAN RTX vendor=0x10de device_id=0x1e02 api_version=4211000 driver_version=2434761728 compile=1 submit=1 fence=1 readback=1 oracle_match=1 batch=3 stages=7 fixture_id=ntt-v1-p97-i29-c17-q3329
PASS backend=vulkan operation=forward device=1 name=NVIDIA RTX A6000 vendor=0x10de device_id=0x2230 api_version=4211000 driver_version=2434761728 compile=1 submit=1 fence=1 readback=1 oracle_match=1 batch=3 stages=7 fixture_id=ntt-v1-p97-i29-c17-q3329
PASS backend=vulkan operation=inverse device=0 name=NVIDIA TITAN RTX vendor=0x10de device_id=0x1e02 api_version=4211000 driver_version=2434761728 compile=1 submit=1 fence=1 readback=1 oracle_match=1 batch=3 stages=7 fixture_id=ntt-v1-p97-i29-c17-q3329
PASS backend=vulkan operation=inverse device=1 name=NVIDIA RTX A6000 vendor=0x10de device_id=0x2230 api_version=4211000 driver_version=2434761728 compile=1 submit=1 fence=1 readback=1 oracle_match=1 batch=3 stages=7 fixture_id=ntt-v1-p97-i29-c17-q3329
...
vulkan_forward_source_sha256=f29443943a381012f34e26a7ab2ac44bee51338d78662109c47e0182aa1fc668
vulkan_inverse_source_sha256=b1e5a9ed87e4331abb5ac7ab906418aa9e4c927d2e284174990110318382e09c
vulkan_forward_spirv_sha256=0865f588f0825a3ff66a1d5e2cd2a9d0c356bb75b4fceaaf5c2196ffa05f6379
vulkan_inverse_spirv_sha256=07a11b541ef204a4fb6c907338dafc99bdf870d2046edcfad02a3d42dcca2687
vulkan_artifact_dir=/home/ormastes/dev/pub/simple/.claude/worktrees/x25519-paired-timing/build/evidence/x25519mlkem768/vulkan
STATUS: PASS X25519MLKEM768 Vulkan forward/inverse physical evidence
```

This is compile + `spirv-val` + an independent, non-Simple Vulkan
Driver-API probe (compile shader module, submit, fence-wait, device-origin
readback, compare to an independent scalar FIPS-203-style oracle) — not a
copy-and-hope of a stale binary, and not a CPU-mirror pass.

## Real-device pass on the actual target spec (not the "retain blocker" branch)

```
$ SIMPLE_TIMEOUT_SECONDS=0 bin/simple test test/02_integration/os/crypto/x25519mlkem768_vulkan_candidate_spec.spl --no-cache --no-cover-check
Results: 3 total, 3 passed, 0 failed
PASS test/02_integration/os/crypto/x25519mlkem768_vulkan_candidate_spec.spl
```

Reproduced twice, with an `md5sum` + `ls -la --time-style=full-iso`
contamination check on the two `.spv` artifacts immediately before and after
the second run — identical (`24bc022c9d53c2a87d21247b87e88cd9`
forward.spv / `81ec4575ae5a05a57f2bf625b5db2729` inverse.spv, both
unchanged). Because the placed artifacts match the pinned digests exactly and
`vulkan_sffi_is_available()` was independently confirmed truthy in-harness
(above), this is branch 3 — the real device-execution branch with the
literal `artifact_digest`/`kernel_invocations`/`compiled`/`submitted`/
`fence_completed`/`device_readback`/`candidate_oracle_match` assertions all
satisfied — not the self-referential blocked-row branch.

Bonus: copying `ml_kem_ntt_forward.comp`/`ml_kem_ntt_inverse.comp` into this
worktree's `src/os/crypto/x25519_mlkem768/kernels/` (byte-identical to the
snapshot-worktree originals, `diff -q` clean) also flips
`test/01_unit/os/crypto/x25519mlkem768_vulkan_shader_contract_spec.spl` from
red (file missing) to `Results: 3 total, 3 passed, 0 failed`.

## Known unrelated pre-existing failure (not caused by this work, not fixed)

`test/01_unit/os/crypto/x25519mlkem768_vulkan_snapshot_contract_spec.spl`
still fails (`Results: 1 total, 0 passed, 1 failed`). This spec inspects
`vulkan_ntt_provider.spl`'s own source text (constructor/execute/shutdown
ordering via `index_of`), not the SPIR-V artifact. `git diff --stat --
src/os/crypto/x25519_mlkem768/vulkan_ntt_provider.spl` shows that file
already had 25 insertions / 2 deletions **before this session touched
anything** (this session only ever `Read` that file, never `Edit`/`Write`) —
almost certainly a side effect of T-02's crypto_accel session-layer
restoration. Out of scope for this Vulkan-artifact-generation task; flagged
so it isn't mistaken for a regression from this work.

## Historical coefficient-mismatch bug — see the separate closure doc

The barrier-mismatch bug doc found in the snapshot worktree described a
coefficient mismatch (first divergence at forward-stage-1 coefficient 128,
expected 849 vs actual 2202) that consumed its three-retry cap without a
confirmed root cause. This session independently reproduced that exact
signature from scratch (before even finding the snapshot worktree) and
root-caused it to a negative-operand `%` (GLSL `OpSMod`) defect in this
host's NVIDIA Vulkan compute driver path. Full analysis, the fix, and why
today's run of the *original, unmodified* source now passes cleanly (where
the historical 2026-08-03 rerun of what appears to be the same source did
not) is in the dedicated doc:
`doc/08_tracking/bug/x25519mlkem768_vulkan_ntt_negative_modulo_driver_defect_2026-08-05.md`.

## Current state

- Vulkan SPIR-V artifact gap: **CLOSED**. Real GLSL source, check script, and
  freshly-built/verified SPIR-V (bit-identical to the pinned digests) exist
  in this worktree.
- `bin/simple test` on the target integration spec: **PASS**, real
  device-execution branch, reproduced twice with a clean contamination check.
- `x25519mlkem768_vulkan_shader_contract_spec.spl`: now PASS (bonus, from
  restoring the `.comp` source).
- `x25519mlkem768_vulkan_snapshot_contract_spec.spl`: still FAIL,
  pre-existing, unrelated, not touched.

## Resume / reproduction commands

```sh
# Regenerate + physically verify from source (requires glslangValidator +
# spirv-val + a Vulkan-capable device on PATH; GLSLANG_VALIDATOR overrides
# the binary name/path if it isn't installed system-wide):
GLSLANG_VALIDATOR=/tmp/simple_glslang/usr/bin/glslangValidator \
  sh scripts/check/check-x25519mlkem768-vulkan-ntt.shs

# Real integration spec:
SIMPLE_TIMEOUT_SECONDS=0 bin/simple test \
  test/02_integration/os/crypto/x25519mlkem768_vulkan_candidate_spec.spl \
  --no-cache --no-cover-check
```

If `glslangValidator` is not available and cannot be installed
(`apt install glslang-tools`, blocked here by no passwordless `sudo`), that
is the only remaining hard toolchain dependency — everything else needed
(source, probe, script, physical devices) is already present.

## Files touched in this worktree (not committed, per task instructions)

- `src/os/crypto/x25519_mlkem768/kernels/ml_kem_ntt_forward.comp`,
  `ml_kem_ntt_inverse.comp` (new, copied from the snapshot worktree,
  byte-identical, sha256 verified)
- `scripts/check/check-x25519mlkem768-vulkan-ntt.shs` (new, copied,
  executable)
- `build/evidence/x25519mlkem768/vulkan/x25519mlkem768_ntt_forward.spv`,
  `..._inverse.spv`, `x25519mlkem768_vulkan_ntt_probe` (new, gitignored
  build output, freshly built by the script above — not source, not
  committed)
- No changes to `src/lib/gc_async_mut/crypto_accel/*`, the CUDA/Metal
  providers, or any compiler source. `vulkan_ntt_provider.spl` was read only,
  never edited by this session (its pre-existing diff predates this task).
