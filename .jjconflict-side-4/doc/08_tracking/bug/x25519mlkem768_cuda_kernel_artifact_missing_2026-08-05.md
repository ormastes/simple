# X25519MLKEM768 CUDA kernel artifact — RESOLVED (physical evidence); a separate interpreter-extern gap now blocks the Simple spec

Date: 2026-08-05
Worktree: `/home/ormastes/dev/pub/simple/.claude/worktrees/x25519-paired-timing`
Campaign: `.spipe/x25519mlkem768_acceleration/state.md`, AC-5 (CUDA lane)

## Summary

T-02 reported CUDA as BLOCKED because no `.cu`/`.ptx` kernel source and no
`build/evidence/x25519mlkem768/cuda/sm_86.cubin` existed anywhere in this
worktree, and no generation script was found. That reading was correct for
*this worktree's git-tracked history and disk state at the time*, but the
artifact-generation pipeline (kernel source, probe, check script) had
already been produced and validated by an earlier session — it just lives
uncommitted in a different, unrelated worktree
(`/home/ormastes/dev/pub/simple/build/worktrees/simpleos-engine2d-stage4-snapshot/`)
and was never committed to git at any point (confirmed: `git status` shows
`src/os/crypto/x25519_mlkem768/kernels/` as untracked `??` even in that
source worktree, and `git cat-file -e HEAD:...` fails for the same path on
every branch checked). It also never propagated into this worktree's
per-worktree, gitignored `build/` directory.

**Action taken:** the missing pieces were copied into this worktree and the
CUDA evidence was regenerated fresh (not merely copied as a binary blob) with
the real toolchain against the two physical GPUs on this host.

## What was verified (re-derived independently, not trusted from T-02's report)

- `src/os/crypto/x25519_mlkem768/cuda_ntt_provider.spl` (restored by T-02, read
  in full): expects a compiled binary with entries
  `X25519_MLKEM768_CUDA_NTT_FORWARD_ENTRY = "x25519_mlkem768_ntt_forward"` and
  `X25519_MLKEM768_CUDA_NTT_INVERSE_ENTRY = "x25519_mlkem768_ntt_inverse"`, and
  a source digest pin `X25519_MLKEM768_CUDA_NTT_SOURCE_SHA256 =
  e3201ae10f48e284d703cff81d42a02d9ba7f96e4bcc9b03872094b25a5a26aa`.
- `src/os/crypto/x25519_mlkem768/gpu_build_admission.spl` pins the exact
  per-device compiled-artifact digests: `562bfee3e9cd630425a69a5b27a0cc6661f0a00609a85078ef376565fb5b7711`
  for `NVIDIA RTX A6000` / capability `8.6`, and
  `41a90792d1286c42014da98d1205972acbf9d60220981c9cc505dddf2b18069f` for
  `NVIDIA TITAN RTX` / capability `7.5`, built with
  `build_toolchain: "CUDA ptxas 13.0 V13.0.88"`.
- `test/02_integration/os/crypto/x25519mlkem768_cuda_binary_execution_spec.spl`
  reads `build/evidence/x25519mlkem768/cuda/sm_86.cubin`, expects
  `_SM86_CUBIN_SHA256 = 562bfee3e9cd630425a69a5b27a0cc6661f0a00609a85078ef376565fb5b7711`
  (matches T-02's report exactly and matches the admission-policy constant),
  compares forward/inverse NTT output against `os.crypto.ml_kem_ntt.{ntt,
  intt}` (the CPU oracle) via `x25519_mlkem768_ntt_fixture(1)`, and asserts
  `compiled/submitted/fence_completed/device_readback/device_identity>0` plus
  exact value equality — this is a real device-execution assertion, not a
  CPU-mirror.
- Host: `nvcc`/`ptxas` 13.0.88 present at `/usr/local/cuda-13.0/bin/`;
  `nvidia-smi --query-gpu=compute_cap,name` reports `8.6, NVIDIA RTX A6000`
  and `7.5, NVIDIA TITAN RTX` — exactly the two device rows pinned above.

## What was found and restored

A real, previously-built kernel-artifact pipeline exists (uncommitted) at
`/home/ormastes/dev/pub/simple/build/worktrees/simpleos-engine2d-stage4-snapshot/`:

- `src/os/crypto/x25519_mlkem768/kernels/ml_kem_ntt_forward.ptx` — hand-written
  PTX containing both `.visible .entry x25519_mlkem768_ntt_forward(` (line 28)
  and `.visible .entry x25519_mlkem768_ntt_inverse(` (line 113). Its
  `sha256sum` is exactly `e3201ae10f48e284d703cff81d42a02d9ba7f96e4bcc9b03872094b25a5a26aa` —
  matches the provider's pinned source digest exactly.
- `test/fixtures/crypto/x25519mlkem768/cuda_ntt_probe.c` — already present and
  byte-identical (`diff -q` empty) in this worktree; an independent CUDA
  Driver API probe (compile/submit/sync/readback/oracle-compare), not part of
  the Simple provider under test.
- `scripts/check/check-x25519mlkem768-cuda-ntt.shs` — the real generation/
  verification script: for each `nvidia-smi`-reported compute capability it
  runs `ptxas` **twice independently** and `cmp`s the two cubins (determinism
  proof), compiles and runs `cuda_ntt_probe.c` against the actual PTX/cubin on
  the actual device, and only on success copies the cubins to
  `build/evidence/x25519mlkem768/cuda/sm_<arch>.cubin`.

These three files were copied into this worktree (paths above; not committed
per instructions) and the check script was executed fresh, from scratch, on
this host:

```
$ sh scripts/check/check-x25519mlkem768-cuda-ntt.shs
cuda_binary_sha256_sm_75=41a90792d1286c42014da98d1205972acbf9d60220981c9cc505dddf2b18069f
cuda_binary_deterministic_rebuild_sm_75=pass
cuda_binary_sha256_sm_86=562bfee3e9cd630425a69a5b27a0cc6661f0a00609a85078ef376565fb5b7711
cuda_binary_deterministic_rebuild_sm_86=pass
PASS backend=cuda device=0 name=NVIDIA RTX A6000 capability=8.6 compile=1 forward=1 inverse=1 submit=1 complete=1 readback=1 oracle_match=1 batch=3 fixture_id=ntt-v1-p97-i29-c17-q3329
PASS backend=cuda device=1 name=NVIDIA TITAN RTX capability=7.5 compile=1 forward=1 inverse=1 submit=1 complete=1 readback=1 oracle_match=1 batch=3 fixture_id=ntt-v1-p97-i29-c17-q3329
cuda_artifact_dir=/home/ormastes/dev/pub/simple/.claude/worktrees/x25519-paired-timing/build/evidence/x25519mlkem768/cuda
STATUS: PASS X25519MLKEM768 CUDA NTT physical evidence
```

Both cubin sha256 values match the pinned constants exactly, and this run
is fresh (`ptxas` invoked twice per architecture in this process, `cmp`
verified byte-identical, then an independent CUDA Driver-API probe compiled,
submitted, synchronized, read back, and matched a scalar oracle on **both**
physical devices) — not a copy-and-hope of a stale binary. Artifact now on
disk:

```
build/evidence/x25519mlkem768/cuda/sm_86.cubin  sha256=562bfee3e9cd630425a69a5b27a0cc6661f0a00609a85078ef376565fb5b7711
build/evidence/x25519mlkem768/cuda/sm_75.cubin  sha256=41a90792d1286c42014da98d1205972acbf9d60220981c9cc505dddf2b18069f
```

This closes the original blocker exactly as T-02 scoped it: "produce/build
the pinned cubin (expected sha256 562bfee3...5b7711)" — done, with stronger
evidence than a bare hash match (independent non-Simple Driver-API execution
proof on both pinned devices).

## New, separate, precise blocker: interpreter cannot resolve `rt_array_data_ptr_u8`

Running the actual target command:

```
SIMPLE_TIMEOUT_SECONDS=0 bin/simple test test/02_integration/os/crypto/x25519mlkem768_cuda_binary_execution_spec.spl --no-cache --no-cover-check
```

Verdict line:

```
Results: 1 total, 0 passed, 1 failed
FAIL test/02_integration/os/crypto/x25519mlkem768_cuda_binary_execution_spec.spl
  ✗ should load admitted sm86 cubin bytes and execute both NTT entries
    semantic: unknown extern function: rt_array_data_ptr_u8
```

This is **not** the kernel-artifact gap — the artifact now exists at the
right path with the right digest. It is a distinct, pre-existing compiler
defect: `bin/simple test` hard-defaults to the tree-walk interpreter (per
`.claude/rules/testing.md`), and the interpreter's extern dispatch table is a
separate registry from the codegen/JIT runtime-symbol list. Confirmed by
direct source inspection:

- `rt_array_data_ptr_u8` **is** registered as a real runtime symbol for
  codegen/JIT (`src/compiler_rust/common/src/runtime_symbols.rs:140,409`) and
  is used throughout the GPU SFFI layer (`src/lib/gc_async_mut/cuda.spl:17`,
  called from `cuda.spl:80/89/102` — i.e. exactly the
  `rt_cuda_module_load_data_bytes` path that `CryptoCudaSession
  .load_module_binary` calls).
- It has **no interpreter adapter**: `grep -rn "rt_array_data_ptr_u8"
  src/compiler_rust/compiler/src/interpreter_extern/` returns nothing, while
  the interpreter's own `error_utils.rs:23` is exactly the site that formats
  `"unknown extern function: {name}"` — the message seen above. The GPU
  interpreter-extern file (`interpreter_extern/gpu.rs`) has adapters for other
  `rt_cuda_*` calls but not for this pointer-extraction helper.
- This is the same class of defect as the memory note "Unregistered `@extern
  fn` silent-nil — JIT ONLY" / `doc/08_tracking/bug/unregistered_extern_silent_nil_2026-08-01.md`,
  but the opposite failure mode: here the interpreter fails **loudly and
  closed** (`exit 1`, explicit "unknown extern function") rather than
  silently. No bug doc previously covered this specific missing adapter.

This is a compiler/runtime interpreter gap, not a crypto or GPU-artifact
defect, and fixing `src/compiler_rust/compiler/src/interpreter_extern/` is
outside this lane's scope (narrowly the CUDA kernel-artifact generation) and
outside the "do not touch crypto_accel session files / other backends" scope
given for this task. It blocks *this specific SPL test-runner invocation
path* only — it does not block the independent, non-Simple physical evidence
already gathered above.

## Current state

- CUDA kernel artifact gap: **CLOSED**. Real PTX source, probe, check script,
  and freshly-built/verified cubins exist in this worktree (paths above).
  Independent CUDA Driver-API evidence (compile/submit/complete/readback/
  device-identity/oracle-match) exists for both physical GPUs.
- `bin/simple test` on the target integration spec: **BLOCKED**, red for a
  new, different, precise reason — `semantic: unknown extern function:
  rt_array_data_ptr_u8` in the interpreter's extern dispatch, reached via
  `CryptoCudaSession.load_module_binary` → `cuda.spl` →
  `rt_cuda_module_load_data_bytes(rt_array_data_ptr_u8(bytes), ...)`.

## Resume command

Once an interpreter adapter for `rt_array_data_ptr_u8` (and any other
`rt_array_data_ptr_*` helpers hit downstream in the same call) is added under
`src/compiler_rust/compiler/src/interpreter_extern/`, rerun:

```
SIMPLE_TIMEOUT_SECONDS=0 bin/simple test test/02_integration/os/crypto/x25519mlkem768_cuda_binary_execution_spec.spl --no-cache --no-cover-check
```

The non-Simple physical-evidence path can be independently reproduced any
time with:

```
sh scripts/check/check-x25519mlkem768-cuda-ntt.shs
```

(requires `nvcc`/`ptxas`, `nvidia-smi`, and a CUDA-capable device — all
present on this host).

## Files touched in this worktree (not committed, per task instructions)

- `src/os/crypto/x25519_mlkem768/kernels/ml_kem_ntt_forward.ptx` (new, copied
  from the snapshot worktree, sha256 verified against the provider's pin)
- `scripts/check/check-x25519mlkem768-cuda-ntt.shs` (new, copied, executable)
- `build/evidence/x25519mlkem768/cuda/sm_86.cubin`,
  `build/evidence/x25519mlkem768/cuda/sm_75.cubin` (new, freshly built by
  running the script above — gitignored build output, not source)
- No changes to `src/lib/gc_async_mut/crypto_accel/*`, the Metal/Vulkan
  providers, or any compiler source.
