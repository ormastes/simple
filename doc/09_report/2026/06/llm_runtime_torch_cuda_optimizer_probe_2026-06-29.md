# LLM Runtime Torch CUDA Optimizer Probe

- command: `release/x86_64-unknown-linux-gnu/simple run src/app/test/torch_cuda_optimizer_probe.spl --mode=interpreter --clean`
- status: `unavailable`
- reason: `libtorch_unavailable`
- required_gates: `libtorch,cuda,parameter_cuda,autograd_gradient,optimizer_step_decreases_parameter_sum`
- blocked_gate: `libtorch`
- blocked_gates: `libtorch`
- primary_blocked_gate: `libtorch`
- torch_available: `false`
- cuda_available: `false`
- parameter_is_cuda: `missing`
- grad_handle: `missing`
- optimizer_step_attempted: `false`
- before_sum: `missing`
- after_sum: `missing`
- next_action: `build or install the Simple runtime with libtorch symbols available, then rerun the strict Torch optimizer probe`
- exit_code: `0`
- env: `build/llm_runtime_torch_cuda_optimizer_probe/evidence.env`
- log: `build/llm_runtime_torch_cuda_optimizer_probe/probe.log`

This wrapper proves the Simple/libtorch CUDA optimizer lane only when all required gates pass. `unavailable` records the exact missing host/runtime gate and remains a strict-host failure.
