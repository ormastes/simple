# riscv64 freestanding: `_sffi_env_set` is unbacked, so the in-guest parser panics on scope exit (2026-09-01)

Status: **OPEN — newly reached blocker.** It became reachable only because the
module-global-initializer defect above it was fixed; before that, execution
never got this far.

Base: `origin/main` @ `ea48917812b` + `702a3b63505`
(`fix(riscv64): freestanding boot never ran module-global initializers`).
Compiler: the Rust bootstrap seed, freshly built
(`cargo build --release --bin simple` in `src/compiler_rust`, exit 0).
Evidence: in-guest, real OpenSBI v1.4 `fw_payload` handed to QEMU as `-bios`
only. No `-kernel`, no `isa-debug-exit`.

## What moved

Prior state (handed to this lane):

```
FAIL — 2 row(s) checked in-guest under real OpenSBI v1.4 firmware, offender(s):
interpreter row: the interpreted hello world did not print its own nonce-carrying output;
build-and-run row: the program was not built and run to a correct result
```

The interpreter guest previously stalled in the parser with
`parser made no forward progress at this token (StringLit '')` — the token
*text*, which lives in the module-level global `core_last_token_text_slot`
(`src/compiler/10.frontend/core/lexer_struct.spl:60`), came back empty because
no `__module_init_*` ran in-guest.

**That symptom is gone.** With module inits running, the guest now tokenizes,
builds expression arenas, and travels far deeper into the frontend before
failing on a different, specific error.

Artifact evidence on `build/os/riscv64_interp/interp/kernel.elf` (same build
script, same target, same backend):

| probe | before | after |
|---|---|---|
| total symbols | 7167 | 8214 |
| `__module_init_*` | **0** | **121** |
| `__simple_call_module_inits` | absent | present, body `0x7dc` bytes |
| `__module_init_compiler__frontend__core__lexer_struct` | absent | present |

## The new blocker

Verbatim, last line of both guests' serial logs:

```
[PANIC] failed to restore SIMPLE_BOOTSTRAP_LEX_SOURCE for src/os/rv64_interp_hello.spl
```

Raised at `src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl:1441`,
in the **non-transient** branch of `parse_and_build_module`'s scope exit:

```
    if not _sffi_env_set("SIMPLE_BOOTSTRAP_LEX_SOURCE", saved_lex_source):
        panic("failed to restore SIMPLE_BOOTSTRAP_LEX_SOURCE for {path}")
```

A freestanding riscv64 guest has no process environment, so `_sffi_env_set`
cannot succeed. This is the unbacked-extern silent-nil class
(`doc/08_tracking/bug/unregistered_extern_silent_nil_2026-08-01.md`) surfacing
as a hard panic rather than a silent nil, because the call site checks the
result.

Two directions, neither yet evaluated — do not pick one without measuring:

1. Back `_sffi_env_set`/`_sffi_env_get` in the freestanding riscv64 runtime
   with a small in-memory key/value table. The parser only needs set-then-
   restore round-tripping, not a real environ.
2. Route the in-guest parse through the **transient** branch (the `if
   transient_scope:` arm above), which does not touch the environment at all.
   Why the in-guest path takes the non-transient branch has not been
   established.

## Second, separate finding — do not conflate it with the above

The gate's verdict on this run was:

```
ERROR — nothing was checked: the build-and-run guest never reached its entry — no boot rungs on serial (log: build/os/riscv64_interp/run/buildrun-serial.log)
```

That ERROR is **not** the panic. `buildrun-serial.log` contains three
`[interp]`-prefixed rungs and **zero** `[buildrun]` rungs, and ends with the
same panic naming `src/os/rv64_interp_hello.spl` — the *interpreter* row's
program path. `buildrun_sanity_entry.spl` prints only `[buildrun]` prefixes
(lines 86-128) and drives a different program, so the build-and-run guest
appears to be executing the interpreter row's code.

The two `kernel.Image` files are genuinely distinct
(`a2709801bdcdf6f7a24bba33bde35f0c` vs `9a043f98f116149350c8c2422b9e9be7`) and
each `kernel.elf` was verified by the build script to contain its own row
symbol, so this is not a build-side mixup of the ELFs. The suspects are the
per-row OpenSBI `fw_payload` embed and the freestanding link's
`--defsym spl_start=<mangled>__spl_start` entry selection. **Not diagnosed** —
a byte-probe of the two `fw_payload.bin` files was inconclusive because the
sampled range is common runtime code present in both. This is exactly hazard 2
("stale OpenSBI firmware — assert positively that the firmware embeds YOUR
Image") and needs a positive, nonce-anchored assertion, not a spot check.

## Reproduce

```
cd src/compiler_rust && cargo build --release --bin simple   # seed, exit 0
sh scripts/os/build-simpleos-riscv64-interpreter-kernel.shs  # ~25 min per row
sh scripts/check/check-simpleos-riscv64-interpreter-in-guest-opensbi.shs
```

The gate's own selftest (23 fixtures) passes unchanged; nothing in it was
weakened.
