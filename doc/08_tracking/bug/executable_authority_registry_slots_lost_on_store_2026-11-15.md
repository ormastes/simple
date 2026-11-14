# Executable authority registry loses its issued slot: commit returns InvalidToken

- **Status:** open (2026-11-15)
- **Where:** `src/os/kernel/loader/executable_authority_registry.spl`
  `executable_authority_issue_verified` (store at `_authority_registry_state = Some(state)`)
- **Reproducer:** `test/01_unit/os/kernel/loader/managed_workload_launch_spec.spl`
  (3/5 RED, -13), and downstream `container_runtime_spec`, `runtime_provider_v1_spec`,
  `macos_simpleos_guest_dispatch_v1_spec` under `test/01_unit/os/services/container/`.

## Proven chain (seed `bin/simple`, macOS)
1. The cap gate is fixed (`cap_fileexec_dir_prefix_denies_children_2026-11-15.md`).
2. Scheduler adoption -> `executable_loader_commit` -> `Err(InvalidToken)`, because
   `_authority_token_index` sees `state.slots.len() == 0`.
3. Inside the issue function, `state.slots.len() == 1` right before
   `_authority_registry_state = Some(state)`, and `next_nonce_counter` advances.
4. In the `_authority_unlock()` that ends the issue call, the global reads
   `slots.len() == 0` but `next_nonce_counter == 2`. The store keeps the scalar
   field and drops the pushed array element.

So the bug is in how `var state = current` (bound by a `match` on a module-level
`Option<struct>`), followed by `state.slots.push(...)` and `global = Some(state)`,
persists the array. It looks like an interpreter value or alias bug, not registry logic.
Only init assigns `slots: []`, and the mutex and counter show a single instance.

## Unblock
Write a standalone repro with no `os.*` imports: a module `var g: S? = nil`, then
match, `var s = cur`, `s.xs.push(x)`, `g = Some(s)`, and read back in another fn.
Then fix at the interpreter layer. A field rebind (`var grown = state.slots; grown.push; state.slots = grown`)
was tried once and did not turn the spec green. It was not separately probed, and it was reverted.

## Also
`container_runtime_spec` never calls `executable_loader_authority_owner_initialize`
(owner lookup -> `InvalidRegistry`). The reference spec does this in `_ensure_authority_registry()`.
