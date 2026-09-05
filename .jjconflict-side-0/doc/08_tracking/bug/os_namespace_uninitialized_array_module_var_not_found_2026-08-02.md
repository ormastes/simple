# `os.*` module-level uninitialized array `var` is unresolvable

Filed 2026-08-02. Base `a19ce60e1d`. Engine: Rust seed (`bin/simple`), interpreter path.

## Verdict

**Compiler defect, not a module defect.** The declaration form is valid Simple
and works everywhere except the `os.*` namespace. Nothing is wrong with
`src/os/sosix/share.spl`.

**UNVERIFIED FIX.** The defect is in the Rust seed. Verifying a change there
needs a bootstrap, which this lane is forbidden to run, so no patch is applied.
Mechanism and repro below are PROVED; any proposed patch is not.

## Symptom

```
error: semantic: variable `sosix_dataset_active` not found
```

`sosix_dataset_active` **is** declared, at `src/os/sosix/share.spl:33`, and used
at lines 66, 139, 165, 166 and 209 of that same file.

## Minimal repro — 4 lines

`src/os/kernel/_bq.spl`:

```
var q_active: [bool; 64]

fn q_init():
    q_active[0] = false
```

Driver:

```
use os.kernel._bq.{q_init}

fn main():
    q_init()
    print("OK")
```

`bin/simple run` on the driver exits 1 with ``variable `q_active` not found``.

## Discriminator — PROVED

Byte-identical file content placed at different paths. This is the whole
finding: the code is not the variable, the location is.

| module path | import namespace | result |
|---|---|---|
| `src/os/kernel/_bq.spl` | `os.kernel.*` | **FAILS** |
| `src/os/sosix/_bz.spl` | `os.sosix.*` | **FAILS** |
| `src/lib/nogc_sync_mut/_bq.spl` | `std.nogc_sync_mut.*` | works |
| `src/lib/common/_bq.spl` | `std.common.*` | works |
| scratch dir outside the repo | `zmods.*` | works |

Three further axes, all under `src/os`, isolate the required shape. **All three
conditions must hold**; relax any one and it works:

| variant | result |
|---|---|
| array, **no** initializer — `var a: [bool; 64]` | **FAILS** |
| array, **with** initializer — `var a: [bool; 64] = [false; 64]` | works |
| **scalar**, no initializer — `var f: bool` | works |

So the failure requires: **`os.*` namespace + array type + no initializer.**

Refuted along the way, each by direct test: it is not the declaration form on
its own, not module-level `var` in an imported module, not the 262 KB array,
not the `while`-loop indexed assignment, not a write-only variable, not a
duplicate-symbol collision (there are none), and not the `os.kernel.*` imports
in `share.spl`.

## Where it surfaces

Emitted from the seed interpreter's indexed-assignment path,
`src/compiler_rust/compiler/src/interpreter/node_exec.rs:1208`
(``format!("variable `{}` not found", container_name)``). The container lookup
fails, so the module-level binding is absent from scope at execution time
rather than being mis-typed. A fix belongs wherever `os.*` module-level
declarations are seeded into the interpreter environment — an initialized array
and a scalar both arrive, an uninitialized array does not, which points at a
default-value synthesis step that is skipped for array types on this path.

Do **not** treat "add an initializer" as the fix. It is a workaround for a
compiler bug and would silently paper over it in 104 places.

## Blast radius — 104 declarations in 10 files

Every module-level uninitialized array `var` under `src/os/` is unresolvable.
Predicate: `^var NAME: [T; N]` with no `=`. Pin `/usr/bin/grep`.

| file | count |
|---|---|
| `src/os/kernel/ipc/message_buffer.spl` | 32 |
| `src/os/sosix/share.spl` | 21 |
| `src/os/kernel/ipc/process_queue.spl` | 13 |
| `src/os/sosix/dylib_share.spl` | 9 |
| `src/os/sosix/socket_share.spl` | 7 |
| `src/os/sosix/fd_ownership.spl` | 6 |
| `src/os/kernel/ipc/shared_dataset.spl` | 6 |
| `src/os/services/device_registry/registry.spl` | 5 |
| `src/os/kernel/interrupts/irq_routing.spl` | 3 |
| `src/os/kernel/interrupts/idt.spl` | 2 |

Element types: u64 (62), bool (15), u8 (9), u32 (8), u16 (4), i32 (2), and one
each of text, i64, `IdtEntry`, and `fn(TaskContext)`. The last two matter: a
default-synthesis fix must handle a struct element type and a function-pointer
element type, not just integers.

This is the SimpleOS kernel IPC and SOSIX layer — message buffers, process
queues, shared datasets, fd ownership, the IDT and IRQ routing. Any path
reaching these arrays fails at execution.

## How it stayed hidden

The only spec covering this code is
`test/03_system/os/os_storage_spec.spl`, which is a dead-entry-point spec: its
`os_storage_test()` is invoked by nothing, so the file exits 0 having asserted
nothing. See `doc/08_tracking/test/dead_entry_point_specs_2026-08-02.md`. The
defect was found by temporarily wiring that spec up. 104 broken declarations in
the kernel IPC layer sat behind one uninvoked function.

## Next

1. Fix the seed's `os.*` module-level array default synthesis; verify with the
   4-line repro above, which needs no bootstrap to *reproduce* even though a fix
   does to validate.
2. Re-run `os_storage_spec` wired up and confirm its 21 assertions pass.
3. Do not mass-add initializers as a substitute for the fix.
