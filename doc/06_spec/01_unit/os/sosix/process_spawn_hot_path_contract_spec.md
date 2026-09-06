# SOSIX Process Spawn Hot-Path Contract

Source: `test/01_unit/os/sosix/process_spawn_hot_path_contract_spec.spl`

Evidence class: `source-contract`.

## Scenarios

- Pass the existing path buffer directly to the spawn syscall without a second
  hot-path allocation or byte copy.
- Keep kernel argv byte marshaling outside the userspace spawn hot path.

The contract protects the allocation reduction; runtime latency still requires
guest performance evidence.

