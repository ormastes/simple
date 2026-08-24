# Freestanding module-global initializers never run on a lane with no crt0 (2026-08-24)

Status: OPEN — the systemic fix is unmade. One lane (aarch64 Limine) is
worked around correctly; every OTHER crt0-less freestanding lane still has the
bug, and will hit it silently.

## Symptom, and why it is nearly invisible

Every module-level `val`/`var` in a freestanding native build reads its **zero
value** instead of its initializer's result. Nothing fails. Nothing warns. The
link succeeds with 0 undefined symbols. The program runs.

Worked example, from the in-guest MCP server on SimpleOS aarch64:

```
tools/list  ->  {"jsonrpc":"2.0","id":"...","result":0}
initialize  ->  ..."serverInfo":{"name":"0","version":"0"}...
```

`result` is the integer `0` where a 41 KB tool payload belongs, and the server
name and version are the string `"0"`. Both are module-level statics. The
`initialize` response was otherwise **completely correct**, because its result is
assembled from inline literals — so the failure presents as "one handler is
broken", not "no module global in this program was ever initialized".

This cost four debugging attempts on a sibling defect before the shape was
recognised. Budget accordingly: if you see a plausible-looking zero, an empty
collection, or a `"0"` where a configured constant belongs, in a freestanding
build, check this FIRST.

## Root cause

The initializers are generated. They are simply never called, and are then
discarded.

| | count (measured, aarch64 Limine MCP kernel) |
|---|---|
| `__module_init_*` symbols in the object files | **22**, incl. `__simple_call_module_inits` in `_init_all.o` |
| the same symbols in the linked `kernel.elf` | **0** |

`inject_freestanding_module_global_init` runs unconditionally for freestanding
targets (`src/compiler_rust/compiler/src/pipeline/native_project/compiler.rs:613-616`),
and `_init_all.o` always defines the fan-out caller
`__simple_call_module_inits` (`.../native_project/linker.rs:899-977`). What is
missing is the CALL SITE:

- **Hosted targets** get it from the generated main stub —
  `__simple_runtime_init(); __simple_call_module_inits(); spl_main();`
  (`linker.rs:846-849`).
- **Freestanding lanes with a `crt0.S`** get it from crt0.
- **A freestanding lane with neither gets nothing.** The aarch64 Limine lane is
  exactly that: Limine's ELF loader jumps straight to a Simple `fn _start()`
  (`examples/09_embedded/simple_os/arch/aarch64/limine_entry.spl`), with no C or
  asm boot glue at all — by design.

With no reference to the chain, `--gc-sections` discards all of it. That is why
the symbols are present in the objects and absent from the image.

**This was already documented in situ and not recognised as general.**
`src/os/kernel/boot/mmio.spl:75` says, of its own module global: *"the
`var _mmio_test_mode: bool = false` default above never executes"* — and the
kernel hand-works-around it in Step 0 of its boot sequence
(`mmio_disable_test_mode()`). One subsystem carried a bespoke workaround for a
whole-program defect.

## Current state

- **aarch64 Limine lane: FIXED** (`ffdf1b37d19`). `limine_aarch64_boot_sequence()`
  declares and calls `__simple_call_module_inits()` itself. Because it is a
  fan-out over every linked module, this is a general capability for that lane,
  not an MCP-specific patch — the plain kernel gets it too, and `mmio.spl`'s
  declared default is now genuinely applied.
- **Every other crt0-less freestanding lane: STILL BROKEN.** Each must currently
  make the same one-line call by hand, and nothing tells an author that.

## The fix site (Rust seed — a DIFFERENT lane)

`wrap_entry_script_as_main` / the entry-closure path in
`src/compiler_rust/compiler/src/pipeline/native_project/compiler.rs:608-612`
should emit the `__simple_call_module_inits()` call into the synthesized
freestanding entry wrapper, exactly as the hosted main stub already does at
`linker.rs:848`. That makes the call unconditional for every freestanding entry
and removes the per-lane obligation entirely.

Not done here, deliberately: `src/compiler_rust` is the Rust seed, which per
`CLAUDE.md` is bootstrap-only and a separate lane from pure-Simple work.

## Ordering constraint any fix must preserve

The call is not safe to place arbitrarily early. An initializer is **arbitrary
Simple code**:

- It must run **after** the platform's MMIO/serial init, because it may touch
  MMIO and it may trap — and a trap before serial is up is an invisible wedge,
  indistinguishable from a hang.
- It must run **before** anything reads a module global, which in practice means
  as early as the above allows.
- It must run **after** the allocator is usable. The aarch64 Limine lane has no
  hazard here (its `rt_alloc` is a bump allocator over a fixed physical range,
  live from the first instruction), but **a lane whose allocator needs its own
  init must run that init first.** A seed-side fix that emits the call at the
  very top of the entry wrapper would break such a lane.

See also: `module_init_order_alphabetical_not_dependency_aware_2026-08-24.md`,
and `doc/05_design/os/simpleos/mcp_in_guest_qemu_2026-08-23.md` status update
2026-08-24 (6) for the full measurement and evidence.
