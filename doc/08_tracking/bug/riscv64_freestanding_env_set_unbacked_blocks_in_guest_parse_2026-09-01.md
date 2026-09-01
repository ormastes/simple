# riscv64 freestanding: `_sffi_env_set` is unbacked, so the in-guest parser panics on scope exit (2026-09-01)

Status: **RESOLVED 2026-09-01 (`aac4ad219da`).** Two successor defects, reached
only after this one was fixed, are recorded at the end of this file and are
OPEN. This blocker itself became reachable only because the
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

## RESOLVED 2026-09-01 (`aac4ad219da`) — and what it uncovered

Both items in this record are fixed.

**The env blocker** is backed by a fixed-capacity guest-local table in
`baremetal_runtime_core.inc.c` (direction 1 above; direction 2 was not taken —
it needed an unbounded investigation into why the in-guest parse chooses the
non-transient arm). A key never set still reports absence, so the property the
old stub comment protected — "set to empty" stays distinguishable from "not
set" — is preserved, and no inherited process environment is fabricated. The
`failed to restore SIMPLE_BOOTSTRAP_LEX_SOURCE` panic no longer appears on
either guest.

**The build-and-run mixup is diagnosed, and it was a gate defect, not a guest
one.** The marker probe this record asked for:

| payload | `HELLO_INTERP_SIMPLEOS_RISCV64` | `BUILDRUN` |
|---|---|---|
| `interp-fw_payload.bin` | 2 | 0 |
| `buildrun-fw_payload.bin` | **2** | **0** |

The build-and-run firmware embedded the *interpreter* row's Image. Cause:
OpenSBI embeds its payload with `.incbin "$(FW_PAYLOAD_PATH)"` and does **not**
list that path as a prerequisite of `fw_payload.o`. Its make is incremental, so
the second row's build found the object up to date and reused the first row's
Image. Neither the ELFs nor the Images were at fault — both were correct and
distinct all along, which is why every build-side check passed.

Fixed in the gate: the firmware objects are deleted before each row's make, and
a **positive** assertion now requires that row's whole flat Image to appear
verbatim inside its firmware. A firmware that merely built cleanly is no longer
accepted as evidence it carries the right payload. After the fix
`buildrun-serial.log` carries 5628 `[buildrun]` lines and zero `[interp]`
lines. The gate's 23 selftest fixtures still pass; a check was added, none
relaxed.

## Current verdict, and the next two defects

```
FAIL — 2 row(s) checked in-guest under real OpenSBI v1.4 firmware (nonce 1abc472f02598fb1), offender(s):
interpreter row: the interpreted hello world did not print its own nonce-carrying output;
build-and-run row: the program was not built and run to a correct result
```

Both rows are evaluated again (recovered from the intermediate ERROR), and both
now fail on new, deeper, *different* errors. The original empty-token-text
stall is gone and has not returned.

**Interpreter row** — reaches HIR lowering and is rejected there:

```
[interp] lowering hello-world source through the real frontend
[interp] FAIL hir lowering error: missing importing module surface for src/os/rv64_interp_hello.spl
[interp] interpreter row exited rc=nonzero
```

Parsing now completes; the failure has moved a whole phase later. Not
investigated.

**Build-and-run row** — reboot-loops. Its three boot rungs repeat 5628/3 times,
so the guest restarts after `[buildrun] lowering source through the real
frontend` rather than progressing or halting. Not investigated; the repetition
means a trap-and-reset, so the next step is a `-d int,guest_errors` run to name
the fault, not more source reading.

### Build-and-run row: the loop's fault is now named

`-d int,guest_errors` over the existing `buildrun-fw_payload.bin` (no rebuild;
`-no-reboot` was already set, so this is the guest re-entering its own entry,
not a machine reset). Filtering to the kernel's address range — the many
`illegal_instruction` traps at `0x80009f0c`/`0x8000b1xx` are OpenSBI's own
`mhpmcounter` CSR probing inside firmware and are normal:

```
   1208 epc:0x00000000802df43c, tval:0x0000000000000000, desc=fault_store
      1 epc:0x00000000802df640, tval:0x0000000000000000, desc=fault_store
```

`tval = 0` is a store through a NULL pointer, and `nm -n` places `0x802df43c`
inside:

```
compiler__frontend__core__lexer_struct__make_core_lexer
```

So the build-and-run row faults while CONSTRUCTING the lexer, one repetition
per loop iteration. Same file as the original defect
(`src/compiler/10.frontend/core/lexer_struct.spl`) but a different failure: a
null *store* during construction, not an empty *read* of an uninitialised
global. The interpreter row gets past this point, so whatever is null here is
reached only on the build-and-run path. Next step is to identify which store in
`make_core_lexer` is at that offset; not done here.
