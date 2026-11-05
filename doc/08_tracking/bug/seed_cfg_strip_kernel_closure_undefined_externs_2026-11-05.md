# Seed semantic check cannot close kernel files on x86_64 host (cfg-strip leak)

Status: open. Priority: P1 toolchain evidence blocker. Owner: seed cfg strip
(pure-Simple `src/compiler` fix; the Rust seed is not patched).

Observed 2026-11-05: `simple compile <any kernel loader/scheduler file>.spl
--format=smf` (Rust seed, x86_64 Linux host) fails with
`semantic: Undefined("undefined identifier: rt_arm64_user_as_create")` —
identical at HEAD without local changes (calibrated via `git stash`).

Root cause is already diagnosed in-code:
`src/os/kernel/memory/user_address_space.spl:16-20` NOTE(cross-arch import
leak) — the seed's cfg strip does not remove `@cfg(arm64)`/ `@cfg(riscv64)`
bodies (or cfg-gated top-level `use` lines), so host compiles pull ARM64
externs (`rt_arm64_user_as_create`, `rt_arm64_user_as_map_page`,
`rt_arm64_stage_elf64_load_image`, ...) and RISC-V inline asm into every
x86_64 semantic closure. The leak chain is long: after stubbing the first
symbols diagnostically, the next undefined symbols appear from arm64 staging
and baremetal net/idt modules; neutralizing the whole chain would require
stubbing dozens of foreign-arch symbols, so the closure cannot be semantic-
checked host-side with the seed.

Impact:
- The SimpleOS managed-container launch repair
  (`doc/08_tracking/bug/simpleos_managed_container_launch_authority_mismatch_2026-09-27.md`)
  resolves every loader symbol by construction (no reference to the removed
  `fs_exec_register_image_with_spawn_spec` remains), but a full host-side
  semantic PASS is unavailable until an admitted self-hosted CLI exists.
- `--target aarch64` does not help: the externs are demanded in the semantic
  phase even for their native target in SMF mode.

Acceptance: with an admitted Stage-3/4 CLI deployed at
`bin/release/<triple>/simple`, `simple check src/os/kernel/loader` and the
managed workload launch spec pass on the x86_64 host with no diagnostic
stubs.
