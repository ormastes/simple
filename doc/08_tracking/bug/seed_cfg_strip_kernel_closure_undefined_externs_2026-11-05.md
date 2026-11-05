# Seed semantic check cannot close kernel files on x86_64 host (cfg-strip leak)

Status: fixed (seed type checker), 2026-11-05. Priority: P1 toolchain
evidence blocker. Owner: seed type checker
(`src/compiler_rust/type/src/checker_check.rs`).

Observed 2026-11-05: `simple compile <any kernel loader/scheduler file>.spl
--format=smf` (Rust seed, x86_64 Linux host) fails with
`semantic: Undefined("undefined identifier: rt_arm64_user_as_create")` —
identical at HEAD without local changes (calibrated via `git stash`).

Root cause (corrected 2026-11-05; the original cfg-strip diagnosis below was
WRONG for current HEAD): the fn-level cfg strip works -- a wrong-arch body
with an undefined identifier compiles cleanly on this host, and
`Undefined("undefined identifier: rt_arm64_user_as_create")` reproduces with
NO `@cfg` involved at all. The actual defect is in the seed's type checker:
`TypeChecker::check_node` (`src/compiler_rust/type/src/checker_check.rs`) had
no `Node::Extern` arm in its statement pass, so an `extern fn` declaration
INSIDE a function body (the parser emits `Node::Extern` there too, e.g.
`src/os/kernel/memory/user_address_space.spl:47`) fell into the `_ => Ok(())`
wildcard and never bound the extern name. The very next call to the extern
then aborted the unit with `Undefined("undefined identifier: ...")`
(`src/compiler_rust/type/src/checker_infer.rs:38`). Top-level externs were
unaffected because the checker's module-level first pass binds them.

This also explains the "--target aarch64 does not help" observation: with an
aarch64-effective target the `@cfg(arm64)` bodies are ACTIVE and are checked,
and their body-local extern declarations hit the wildcard.

Fix: `checker_check.rs` `check_node` now binds `Node::Extern` names that are
not already registered (module-level externs keep their first-pass binding
unchanged; body-local ones are bound for the enclosing scope only, since the
function-body env is cloned/restored). Regression test:
`src/compiler_rust/type/tests/body_local_extern.rs` (3 tests; 2 fail before
the fix with the exact reported error, all pass after).

Note: this patches the Rust seed contrary to the original owner note below;
the seed is the only verifiable lane until an admitted self-hosted CLI
exists, and the language deliberately supports body-local `extern fn`
(widespread across kernel loader files). The pure-Simple compiler should be
checked for parity on the same construct (cf. bug
`pure_simple_nested_extern_registration_2026_10_12`).

Original (incorrect) diagnosis, kept for the record:

Root cause was already diagnosed in-code:
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
