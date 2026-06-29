# LLM Runtime Torch CUDA Optimizer Probe

- command: `release/x86_64-unknown-linux-gnu/simple run src/app/test/torch_cuda_optimizer_probe.spl --mode=interpreter --clean`
- status: `unavailable`
- reason: `libtorch_unavailable`
- required_gates: `libtorch,cuda,parameter_cuda,autograd_gradient,optimizer_step_decreases_parameter_sum`
- blocked_gate: `libtorch`
- blocked_gates: `libtorch`
- primary_blocked_gate: `libtorch`
- python_torch_module_status: `available`
- python_torch_version: `2.9.1+cu130`
- python_torch_cuda_available: `true`
- python_torch_cuda_device_count: `2`
- system_libtorch_status: `missing`
- torch_available: `false`
- cuda_available: `false`
- parameter_is_cuda: `missing`
- grad_handle: `missing`
- optimizer_step_attempted: `false`
- before_sum: `missing`
- after_sum: `missing`
- sum_decreased_status: `not_collected`
- pass_integrity_status: `not_applicable`
- pass_integrity_reason: `not_applicable`
- next_action: `build or install the Simple runtime with libtorch symbols available, then rerun the strict Torch optimizer probe`
- exit_code: `0`
- env: `build/llm_runtime_torch_cuda_optimizer_probe/evidence.env`
- log: `build/llm_runtime_torch_cuda_optimizer_probe/probe.log`

This wrapper proves the Simple/libtorch CUDA optimizer lane only when all required gates pass. A `status=pass` probe log must also include normalized proof fields showing libtorch and CUDA availability, CUDA parameter placement, a nonzero gradient handle, an attempted optimizer step, and numeric `after_sum < before_sum`. `unavailable` records the exact missing host/runtime gate and remains a strict-host failure.
