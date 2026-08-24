# Module-global initializer order is alphabetical, not dependency-aware (2026-08-24)

Status: OPEN — an unconstrained ordering hazard. **Not** a known-broken thing:
no failure from it has been observed. What is established is that nothing
prevents one, and the order that exists is arbitrary with respect to what
initializers actually depend on.

## What was measured (this is settled, not speculated)

The question "is the order defined at all?" has a definite answer: **yes, and it
is alphabetical by sanitized symbol name.**

Statically, `src/compiler_rust/compiler/src/pipeline/native_project/linker.rs`
collects every `__module_init_*` global symbol across the object files into
`init_names` (`:899-928`), then:

```rust
init_names.sort();
init_names.dedup();
```
(`:936-937`), and emits `__simple_call_module_inits` as a straight-line fan-out
in exactly that order (`:964-977`).

Confirmed empirically against the linked artifact rather than trusting the
source — disassembling `__simple_call_module_inits` out of the aarch64 Limine
MCP kernel gives **18 distinct initializers**, and the emitted call sequence is
byte-for-byte the alphabetical ordering of their names.

## Why that is a hazard rather than a bug

Alphabetical order is **deterministic and reproducible**, which is genuinely
valuable — builds do not vary run to run, and a reproducible-build check will
not flap. But it has no relationship to dependency order.

If module `a_config`'s initializer reads a module global owned by `z_registry`,
`a_config` runs first and reads `z_registry`'s **zero value**, silently. The
same code works or breaks depending on the alphabetical accident of the two
module names. Renaming a module can introduce or fix the bug with no other
change.

The failure mode is the same silent-zero shape as the sibling record
(`freestanding_module_inits_not_called_without_crt0_2026-08-24.md`): no
diagnostic, no link error, just a plausible-looking zero or empty collection
some layers away from the cause.

## What has NOT been established

- **No actual cross-module initializer dependency has been found**, in the MCP
  graph or anywhere else. The 18 initializers in the measured kernel were not
  audited for whether any reads another module's global. This record exists
  because the hazard is unconstrained, not because a break was seen.
- Whether the HIR/module layer has any notion of initializer dependency that
  could be used to topologically sort `init_names` is unexamined.
- Behaviour under a cyclic dependency between module initializers is unexamined;
  a topological sort would have to define it.

## Options if this is ever acted on

1. **Topologically sort `init_names`** by inter-module global references, with a
   defined (and diagnosed) behaviour for cycles. Correct, and the most work.
2. **Diagnose rather than reorder** — make the compiler warn or error when a
   module-level initializer reads a global owned by a module that sorts later.
   Cheaper, and turns a silent wrong answer into a build-time message, which is
   the property that actually matters here.
3. **Leave it and document it** — the current state, now that this record
   exists.

Note that option 2 alone would have caught the whole silent-zero class, and is
worth weighing first precisely because it does not require getting ordering
right.

## Where the fix would live

`src/compiler_rust/compiler/src/pipeline/native_project/linker.rs:936` (the
`sort()`), plus whatever supplies dependency information. That is the **Rust
seed**, a separate lane from pure-Simple work per `CLAUDE.md`.

Evidence and full context:
`doc/05_design/os/simpleos/mcp_in_guest_qemu_2026-08-23.md`, status update
2026-08-24 (6).
