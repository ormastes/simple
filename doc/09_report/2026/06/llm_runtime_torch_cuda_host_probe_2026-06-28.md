# LLM Runtime Torch CUDA Host Probe - 2026-06-28

## Scope

This report records host evidence for `FR-LLM-RUNTIME-0003`. It is not
completion evidence for live Simple/libtorch optimizer execution.

## Commands

```sh
release/x86_64-unknown-linux-gnu/simple test test/01_unit/lib/common/torch/dyn_sffi_ops_readiness_spec.spl --mode=interpreter --clean
```

```sh
python3 - <<'PY'
import json, shutil, subprocess, torch
print(json.dumps({
  "python_torch_import": "ok",
  "python_torch_version": torch.__version__,
  "python_torch_cuda_available": str(torch.cuda.is_available()).lower(),
  "nvidia_smi": "ok" if shutil.which("nvidia-smi") else "missing",
}, sort_keys=True))
PY
```

## Result

The Simple dynamic Torch SFFI readiness spec passed:

```text
Files: 1
Passed: 5
Failed: 0
```

The local Python/CUDA probe reported:

```json
{"nvidia_smi":"ok","nvidia_smi_code":0,"nvidia_smi_stdout":["NVIDIA RTX A6000","NVIDIA TITAN RTX"],"python_torch_cuda_available":"true","python_torch_import":"ok","python_torch_version":"2.9.1+cu130"}
```

## Interpretation

The host has CUDA-capable Python Torch and visible NVIDIA GPUs, and the Simple
dynamic Torch SFFI boundary still passes its readiness spec. `FR-LLM-RUNTIME-0003`
remains `request` because the required evidence is a Simple/libtorch CUDA
optimizer step, not only Python Torch availability or placeholder optimizer
tests.
