# Executable authority registry loses its issued slot: commit returns InvalidToken

- **Status:** closed (2026-11-15) - fixed in the seed interpreter; see "Fix"
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

## Root cause (2026-11-15)
Seed interpreter, `src/compiler_rust/compiler/src/interpreter_patterns.rs`
`merge_match_arm_subject_bindings`. After a match arm runs, the interpreter merges
container fields from the payload binding (`current`) back into the match subject
place (`_authority_registry_state`). The arm had already stored a new value into
that place. The merge then copied the stale binding's empty `slots` array over it.
Scalar fields were not merged, which is why `next_nonce_counter` survived.

Minimal repro, no `os.*` imports: in a fn, `match g: case Some(cur): var s = cur;
s.xs.push(x); g = Some(s)`. Reading back gives `len=0`. The registry code was correct.

## Fix
When the subject place's post-arm value differs from the pre-arm subject, the arm
stored to it explicitly. That store wins, and the payload merge is skipped.
The merge still runs when the arm only mutated through the binding.

- Rust test: `match_arm_store_into_subject_global_is_not_rewound_by_payload_merge`
  (`interpreter_patterns::tests`, 41/41 pass).
- Repro + generalization spec:
  `test/01_unit/interpreter/match_arm_subject_store_not_rewound_spec.spl`.
  Old seed: 2/3 (repro RED). Rebuilt seed: 3/3.
- Registry probe: `token_index` now reads `slots=1` after issue. It read `slots=0` before.

## Not this bug (still RED on macOS arm64)
After the fix, the launch specs still return -13. The cause is now different:
adoption fails with `RollbackUnavailable`, because `get_arch()` is Arm64 on this
host and the specs hand it an x86_64 ELF with `Architecture.X86_64`. Filed as
`managed_workload_launch_specs_x86_64_only_on_arm64_host_2026-11-15.md`.
Also: `vmm_new_process_space` was private but imported through the `vmm` facade
by `syscall_spm.spl`, so the specs failed to load. It is now `pub`.
