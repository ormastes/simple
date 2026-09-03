# Agent Tasks: LLM Build Progress Surface

- **Contract owner:** model, codec, monotonic admission.
- **Compiler owner:** `log_build_progress` projection.
- **Bootstrap owner:** centralized path/build identity wiring.
- **CLI owner:** bounded reader and concise output.
- **Review owner:** SPipe, mutation, direct-env, native-build observation.

Merge owner and final reviewer must be different. Parallel sidecars are N/A for the initial narrow seam because shared contracts and one compiler call site dominate the change.

