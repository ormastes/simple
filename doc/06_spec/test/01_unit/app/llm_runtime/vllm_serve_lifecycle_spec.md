# vLLM Serve Lifecycle Wrapper Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

## Scenarios

- Failed serve plans do not spawn.
- Successful spawned pids become started lifecycle evidence.
- Spawn failures are explicit.
- Invalid pids are not polled as live processes.
- Invalid pids are not killed.

## Source

`test/01_unit/app/llm_runtime/vllm_serve_lifecycle_spec.spl`
