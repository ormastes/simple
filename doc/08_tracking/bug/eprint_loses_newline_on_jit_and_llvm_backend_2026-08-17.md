# `eprint` loses its trailing newline on the JIT and the LLVM backend (interpreter is correct)

- **ID:** eprint_loses_newline_on_jit_and_llvm_backend_2026-08-17
- **Status:** OPEN — reproduced by probe, root cause located in current source,
  **not fixed** (see "Why no fix landed here" below).
- **Filed:** 2026-08-17
- **Severity:** P2 by blast radius, but it corrupts every native/JIT diagnostic
  stream, which makes it a P1-grade *investigation hazard*: consecutive
  diagnostics run together on one line, so a loop that prints N lines looks like
  it printed one, or none.
- **Area:** `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl:1603`
  (builtin-call name mapping); the Rust seed's Cranelift JIT has the same
  behaviour.

## Reproduction

Probe (four statements, no imports):

```
fn main():
    eprint("A")
    eprint("B")
    print("C")
    print("D")
```

Binary that produced these numbers — stated because `bin/simple` is a **stale
Rust seed** and a result from it is evidence about that binary, not about current
source:

```
$ readlink -f bin/simple
/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple
$ stat -c '%s %y' "$(readlink -f bin/simple)"
59536728 2026-08-16 22:59:37.799277177 +0000
```

Byte-exact output (`od -c`, so this is not a display artifact and not a pipe
artifact — `tail`/`od` preserve newlines):

| engine | bytes emitted after the seed's banner |
|---|---|
| `env SIMPLE_EXECUTION_MODE=jit bin/simple run` | `A B C \n D \n` — i.e. `ABC\nD\n` |
| `env SIMPLE_EXECUTION_MODE=interpreter bin/simple run` | `A \n B \n C \n D \n` |

So under the JIT, **`eprint` emits no trailing newline** (`A` and `B` concatenate,
and the `\n` that follows `C` is `print`'s own). `print` is correct on both
engines. The interpreter is correct on both calls.

## Root cause in CURRENT SOURCE (not just the stale seed)

This is not a seed-only artifact. `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl:1603`
maps the language builtin `eprint` to the **no-newline** runtime entry point:

```
... elif bare_name_for_call == "eprint": "@rt_eprint" ...
```

and the two places that emit the LLVM declarations declare both variants side by
side, so the newline-appending one is available and simply not selected:

- `src/compiler/70.backend/backend/llvm_backend.spl:466-467`
- `src/compiler/70.backend/backend/llvm_backend_tools.spl:327-328`
- `src/compiler/70.backend/backend/llvm_lib_translate.spl:370-373`

The runtime side confirms the two names differ exactly by the newline —
`rt_eprintln_str` is literally `rt_eprint_str` plus a newline
(`src/runtime/runtime_native.c:5144-5150`):

```
void rt_eprint_str(const uint8_t* ptr, uint64_t len) { ... }
void rt_eprintln_str(const uint8_t* ptr, uint64_t len) {
    rt_eprint_str(ptr, len);
    ...
}
```

Note also that the bare `rt_eprint(ptr)` / `rt_eprintln(ptr)` symbols the LLVM
backend *declares* are not defined in `src/runtime/runtime_native.c` (only the
`_str` and `_value` forms are), so whether the native lane resolves them from the
Rust runtime is worth checking as part of any fix.

## Candidate fix (deliberately NOT applied)

Change the mapping at `core_codegen.spl:1603` from `@rt_eprint` to `@rt_eprintln`
so all three engines agree, and make the Cranelift/JIT builtin binding do the
same.

## Why no fix landed here

Two reasons, both about not manufacturing a false green:

1. The change cannot be verified from this checkout. Confirming it requires a
   native/LLVM build, and this checkout is shared by ~15 concurrent lanes that
   must not have `bin/simple` / `bin/release/**` rebuilt or redeployed under
   them. Landing an unverified one-line codegen change would be exactly the
   "fix that was never executed" failure mode.
2. Two other `eprint` rows are already open and at least one was filed the same
   day, so an active lane is likely holding these files:
   - `doc/08_tracking/bug/stdlib_eprint_shadows_prelude_builtin_program_wide_2026-08-17.md`
   - `doc/08_tracking/bug/eprint_in_io_runtime_module_is_rerouted_to_stdout_2026-08-10.md`
   Whoever fixes those should fold this mapping in, since all three are the same
   question — "which `eprint` does a call site actually reach, per engine".

## Why this matters beyond cosmetics

It manufactures phantom bugs. A diagnostic loop of the shape
`while i < n: eprint("[tag] i={i} ...")` produces one unbroken line under
JIT/native, which reads as "the loop body never ran". That is the reported
symptom shape of
`doc/08_tracking/bug/stage3_selfhost_phase3_error_array_index_after_struct_reassign_silently_noops_2026-08-10.md`
("count=572 printed, zero per-error lines printed"). This bug is **not**
sufficient to explain that row — that row also reports a `file_write()` in the
same position producing no file, which no newline defect can cause — but any
re-investigation of it must rule this out first, and should not trust
`eprint`-based instrumentation on a native binary at all.

## Related

- `stage3_selfhost_phase3_error_array_index_after_struct_reassign_silently_noops_2026-08-10.md`
  (symptom shape; still OPEN — the reassign-then-index shape itself does **not**
  reproduce on either seed engine, see that row's 2026-08-17 note)
- `stdlib_eprint_shadows_prelude_builtin_program_wide_2026-08-17.md`
- `eprint_in_io_runtime_module_is_rerouted_to_stdout_2026-08-10.md`
