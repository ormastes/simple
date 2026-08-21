# `SIMPLE_EXECUTION_MODE` — selecting the execution lane

`SIMPLE_EXECUTION_MODE` picks which lane the driver executes Simple code on.
Unset, it defaults to the JIT (Stage 2+).

## Valid values

| value | lane |
|---|---|
| `jit` | default JIT |
| `interpret` | tree-walk interpreter |
| `interpreter` | alias of `interpret` |
| `interpret-optimized` | interpreter, optimized interpreter_mode |
| `cranelift` | Cranelift JIT |
| `llvm` | LLVM JIT |
| `vhdl` | selects the VHDL *backend*; execution lane stays the JIT |
| `wasm`, `wasm32`, `wasi`, `wasm32-wasi` | WebAssembly under a WASI host |

Matching is **case-sensitive**: `JIT` is rejected, `jit` is accepted.

Source of truth: `ExecutionMode::VALID_MODES` in
`src/compiler_rust/driver/src/exec_core.rs`. A test
(`advertised_valid_modes_are_all_accepted`) asserts every advertised spelling
actually parses, so this table cannot drift from the parser.

**There are two parsers and they must agree.** The pure-Simple CLI keeps its own
list in `src/app/cli/_CliMain/args_and_os_commands.spl` (~:331-345) and had
already fixed this same silent-fallback defect on its side, warning instead of
substituting. That list was the LARGER one — it recognised `interpret-optimized`
and `vhdl`, which the Rust parser did not. Rejecting a mode the Simple lane
documents would kill a supported workflow at exit 2, so the Rust set was widened
to match, and the test `accepts_every_mode_the_pure_simple_cli_recognises` pins
the agreement. Add a mode to one list and that test fails until you add it to
the other.

`interpret-optimized` is an **interpreter** mode. The Rust parser previously
routed it to the JIT through the catch-all — the same substitution bug — so it
now correctly yields the interpreter lane.

## Unknown values are rejected, loudly

```
$ SIMPLE_EXECUTION_MODE=interp bin/simple lint foo.spl
error: unknown SIMPLE_EXECUTION_MODE="interp"; valid values are: jit, interpret, interpreter, interpret-optimized, cranelift, llvm, vhdl, wasm, wasm32, wasi, wasm32-wasi
$ echo $?
2
```

**This used to fail silently and it corrupted a measurement.** `parse_str`
mapped `_ => ExecutionMode::Jit`, so any unrecognised value — including the
plausible abbreviation `interp` — quietly selected the JIT. On 2026-08-21 that
produced a published "interpreter" peak-RSS figure of 0.86 GB / 15.4s which was
really a JIT run; the true interpreter figure for the same file is 0.69 GB /
338s. Nothing in the output distinguished the two. The only tell was that the
"interpreter" wall time matched the JIT run almost exactly.

A silent fallback on a *mode selector* is uniquely dangerous: you cannot tell
from the results which lane produced them, so every downstream number inherits
the mistake. Hence fail-closed with exit code 2.

Note `jit` is now an explicitly listed value. It previously "worked" only by
falling through the catch-all, which made it indistinguishable from a typo.

## When benchmarking

- Always use `interpret` (or `interpreter`), never `interp`.
- Sanity-check the wall time. The interpreter is roughly 20x slower than the JIT
  on a large file; if your "interpreter" run finishes as fast as the JIT one,
  you are measuring the JIT.
- Pair the mode with `SIMPLE_MEM_TRACE=1` to get the allocation census, which
  reports `module_loads`, per-phase retention, and the top retaining modules at
  process exit.

See also:
`doc/08_tracking/bug/memory_retention_compiler_and_interpreter_2026-08-21.md`.
