# Blocked: live-capture spec for `ml_profile` typed-evidence adapter (T2g)

Task: `doc/03_plan/infra/sspec/modern_sspec_completion_plan_2026-08-09.md` T2g
asked for a LIVE-capture spec for `src/lib/common/spec/evidence/format/ml_profile.spl`
(`MlRun`/`MlMetric`/`ml_run_to_evidence`), replacing hand-built metric records
with a real driven ML run — same shape as the `audio_profile` live spec landed
alongside this doc at
`test/03_system/tools/spipe/examples/live_audio_capture_spec.spl`.

## Gap

No real, spec-reachable model-run facade exists in this repo that produces
metrics from an actual inference/training run under the spec/test runtime.
The only ML/tensor facade is `src/lib/gc_async_mut/torch/{mod,torch_training,
backend,optim}.spl`, which is a real libtorch FFI binding (backed by
`src/runtime/torch_sffi.cpp` / `torch_sffi.h`), not a synthetic stub — but it
requires the native `rt_torch_*` extern surface to be linked and initialized,
and that extern surface is NOT resolvable from the interpreter runtime specs
run under (`bin/simple test`).

Evidence — the existing torch unit spec is already marked skipped for exactly
this reason:

```
test/01_unit/lib/torch_spec.spl:1-4
describe "Torch":
    it "skipped":
        val pending_reason = "interpreter runtime issue: semantic: unknown extern function: rt_torch_available"
        expect(pending_reason.len()).to_be_greater_than(0)
```

Searches run (bounded, ~15 min):

```
$ /usr/bin/grep -rl "fn.*_run\|InferenceResult\|model_run\|onnx_run\|torch_run" src/lib/gc_async_mut --include=*.spl
  -> only unrelated hits (GPU/browser engine, package install, jit_runner) — no ML-run facade
$ find src/lib/gc_async_mut -maxdepth 2 -iname "*ml*" -o -iname "*torch*" -o -iname "*onnx*"
  -> src/lib/gc_async_mut/torch  (real libtorch FFI, extern-gated — see above)
$ /usr/bin/grep -n "pub fn" src/lib/gc_async_mut/torch/{mod,torch_training,backend}.spl
  -> torch/mod.spl and torch_training.spl expose classes (Tensor, Linear,
     Conv2d, MSELoss, ...) built on `use std.torch.sffi.{rt_torch_*}` calls;
     backend.spl and torch_ffi.spl have no callable `pub fn` surface reachable
     without the native extern resolving first
```

A spec that hand-computes "metrics" via plain arithmetic (no real
model/dataset run) and feeds them to `ml_run_to_evidence` would be a fixture
dressed as live capture — exactly what T2g says NOT to do (reject that
approach). No other real, reachable ML-run source was found.

## What would unblock it

1. Resolve `rt_torch_available` (and the rest of `rt_torch_*`) under the
   interpreter runtime that `bin/simple test` uses for specs — either wire
   the extern resolution for the interpreter path, or run this spec class
   under a runtime mode where native externs link (e.g. native/JIT build with
   libtorch present), whichever the torch team intends per
   `test/01_unit/lib/torch_spec.spl`'s skip reason.
2. Once `rt_torch_available` resolves, a live-capture ML spec can: build a
   tiny real `Tensor`/`Linear` model via `std.gc_async_mut.torch.mod`, run one
   real forward pass + `MSELoss` via `torch_training.spl`, read back the real
   loss/tensor values, and feed them as `MlMetric.value_scaled` into
   `ml_run_to_evidence` — with the oracle's expected values computed by hand
   from the fixed model weights/inputs, independent of the evidence read
   back, exactly like the pattern used in the landed
   `live_audio_capture_spec.spl`.

## Resume command

```
sh scripts/check/... # n/a — start by re-running:
timeout 60 bin/simple test test/01_unit/lib/torch_spec.spl
# once it no longer reports "unknown extern function: rt_torch_available",
# resume T2g by writing test/03_system/tools/spipe/examples/live_ml_capture_spec.spl
# following the live_audio_capture_spec.spl pattern, driving
# std.gc_async_mut.torch.{mod,torch_training} for a real forward pass into
# std.common.spec.evidence.format.ml_profile.{MlRun, MlMetric, ml_run_to_evidence}.
```
