# Forcing the Interpreter (Execution-Engine Selection)

**One-line answer: `SIMPLE_EXECUTION_MODE=interpret` — nothing else is reliable.**

```bash
SIMPLE_EXECUTION_MODE=interpret bin/simple run prog.spl   # tree-walk interpreter
bin/simple-interp run prog.spl                            # same thing, wrapper
bin/simple run prog.spl                                   # default: Cranelift JIT
```

This page exists because engine selection has been the repo's worst fail-open
surface: three separate knobs that *looked* like they pinned the interpreter and
silently returned JIT results. Every "reproduced under both engines" claim made
with one of those knobs compared JIT against JIT.

## The knobs, and which are real

Measured on the deployed `bin/simple` (2026-07-28) with a differential probe —
`var a = [5]` then `a.get(0)`, which returns `5` on the interpreter and the
tag-boxed `40` on the JIT (bug
`doc/08_tracking/bug/list_get_returns_tag_boxed_value_shifted_left_3_2026-07-28.md`).

| Knob | Works? | Notes |
|------|--------|-------|
| `SIMPLE_EXECUTION_MODE=interpret` | **YES** | The one true knob. Read by `src/compiler_rust/driver/src/exec_core.rs:73` and `src/app/cli/_CliMain/args_and_os_commands.spl:301`. |
| `SIMPLE_EXECUTION_MODE=interpreter` | **YES** | Synonym. Was seed-only until 2026-07-28; the pure-Simple CLI ignored this spelling and silently gave JIT. Fixed. |
| `SIMPLE_EXECUTION_MODE=interpret-optimized` | YES | Interpreter, optimized mode. |
| `bin/simple-interp` | **YES** (since 2026-07-28) | Previously set *nothing* and ran the JIT despite its name. Now exports `SIMPLE_EXECUTION_MODE=interpret`. |
| `SIMPLE_NO_JIT=1` | **NO on the seed**, yes on pure-Simple | It only ever raised the interpreter's internal JIT *threshold* (`src/compiler/10.frontend/core/interpreter/mod.spl:194`) — it never selected the engine. `src/compiler_rust/` has no reader at all. The pure-Simple CLI now maps it to force-interpret; the Rust seed still ignores it. **Do not use it for A/B work.** |
| `--interpret` flag | **NO** | Documented in `doc/07_guide/app/tools/cli.md`, parsed by the pure-Simple CLI, but a no-op on the shipped seed for `run`: before the path it is read as a filename, after the path it is silently discarded. |
| `--no-jit` flag | **NO** | Same as above. In the pure-Simple CLI it sets `SIMPLE_NO_JIT`, which was itself a no-op. |

## Fail-open trap: unrecognized values

`ExecutionMode::parse_str` (`src/compiler_rust/driver/src/exec_core.rs:36-43`)
maps **any** unrecognized string to `Jit`:

```rust
_ => ExecutionMode::Jit,
```

So `SIMPLE_EXECUTION_MODE=interpretr` (typo) runs the JIT and says nothing. The
pure-Simple CLI now prints a stderr warning naming the valid values instead of
falling through in silence; the seed does not. **Verify, do not assume.**

## How to verify you actually got the interpreter

Never trust the knob — trust a differential oracle. Run a case whose two engines
disagree and confirm the value flipped:

```bash
cat > /tmp/engine_check.spl <<'EOF'
fn main():
    var a = [5]
    print "a.get(0)={a.get(0)}"
EOF
bin/simple run /tmp/engine_check.spl                            # a.get(0)=40  (JIT)
SIMPLE_EXECUTION_MODE=interpret bin/simple run /tmp/engine_check.spl  # a.get(0)=5 (interpreter)
```

If both print the same number, your knob did nothing — regardless of what it is
named.

## Two further gotchas

- **The JIT silently demotes to the interpreter on its own.** One unsupported
  operation (`d.insert(...)`), or merely the *text* `std.cli`, `get_cli_args`,
  or `window_winit` appearing in the source, forces the whole program to the
  interpreter (`should_prefer_interpreter_for_source`,
  `src/compiler_rust/driver/src/exec_core.rs:871`). A combined probe file can
  therefore report "both engines agree" for every case in it. Keep each probe in
  its own minimal file.
- **`bin/simple test` is not `bin/simple run`.** The spec runner hard-defaults to
  the tree-walk interpreter and has no JIT variant, so the suite cannot reach the
  engine ordinary programs run on. See
  `doc/08_tracking/bug/run_vs_test_harness_divergence_2026-07-28.md`.

## Related

- `doc/07_guide/runtime/crash_debugging.md` — env toggles for crash bisection
- `doc/07_guide/app/tools/cli.md` — full CLI flag table
- `.claude/rules/testing.md` — engine-parity rules for spec work
