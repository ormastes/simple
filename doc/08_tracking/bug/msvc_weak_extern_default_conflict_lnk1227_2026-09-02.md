# MSVC: `__attribute__((weak))` in runtime_native.c is a fatal LNK1227

- **Filed:** 2026-09-02
- **Status:** OPEN — this is the current blocker for Windows MSVC Stage 2 admission
- **Lane:** Windows MSVC bootstrap, Stage 2 receiver probe (probe 2, the
  positional pure-Simple Stage-3 route)

## Symptom

```
simple_rt_<pid>_x86_64-pc-windows-msvc_runtime_native.obj : fatal error LNK1227:
  conflicting weak extern definition for 'rt_cli_get_args'.
  new default '.weak.rt_cli_get_args.default.rt_random_hex' conflicts with
  previous default '.weak.rt_cli_get_args.default.rt_dir_create_cpath'
  (in ..._runtime.obj)
```

(Message is Korean-locale on this host; grep the code `LNK1227`, never English
words.) `link.exe` exits **1227**.

## Mechanism

`src/runtime/runtime_native.c` marks a large group of functions
`__attribute__((weak))` unconditionally — `spl_init_args`, `spl_arg_count`,
`spl_get_arg`, `rt_get_argc`, `rt_get_args`, `sys_get_args`, `rt_cli_get_args`,
`rt_cli_arg_count`, and ~40 more that `runtime.c` also defines (the link emits
one `LNK4006` per duplicate: `rt_dir_create_cpath`, `rt_is_interpreter_runtime`,
`rt_text_to_bytes`, `rt_file_*`, `rt_bdd_*`, …).

On COFF, clang-cl lowers `weak` to a **weak external** carrying a *default*
fallback symbol name. Two objects that both declare the same weak external with
**different** default symbols is a hard error.

**`/FORCE:MULTIPLE` does not cover this.** That flag downgrades duplicate
*strong* definitions to `LNK4006` warnings — which is exactly what the log shows
happening for ~40 symbols. Conflicting *weak-external defaults* are a separate
rule and are fatal regardless.

`SIMPLE_CORE_C_STANDALONE=1` is being passed and is not suppressing this group.

## Precedent already in the file

`rt_set_args` already has a `#if defined(_WIN32)` **non-weak** carve-out with a
long rationale (runtime_native.c ~5532): on this repo's Windows GNU toolchain a
PE/COFF weak external never resolves cross-TU. That carve-out was made for one
symbol; the same platform reality applies to the whole group, and the MSVC/COFF
half of it is a *different and fatal* failure rather than an unresolved symbol.

## Fix directions (not yet chosen)

1. Extend the `_WIN32` non-weak treatment from `rt_set_args` to the whole
   duplicated group. Cheap, matches existing precedent, but leaves ~40 duplicate
   strong definitions riding on `/FORCE:MULTIPLE`.
2. Better: make `SIMPLE_CORE_C_STANDALONE=1` actually compile these fallback
   copies OUT of `runtime_native.c`, since `runtime.c` defines all of them and
   the LNK4006 lines confirm `runtime.c`'s definition wins every time. That
   removes the duplicates rather than tolerating them.

Whichever is chosen, the non-Windows lanes must stay byte-identical — the
existing comment explains why weak is load-bearing for the Stage4 dual-capsule
Linux/FreeBSD/macOS path (`exact_stage4` links this C archive alongside the Rust
runtime capsule without `-z muldefs`).

## How this became visible

It was invisible until 2026-09-02 because the MSVC link ran through cmd.exe and
its log was always unreadable — see
`windows_cmd_shell_string_mangled_by_argv_quoting_2026-09-02.md`. Once the
linker was invoked directly by argv, the real `LNK1227` line appeared
immediately.
