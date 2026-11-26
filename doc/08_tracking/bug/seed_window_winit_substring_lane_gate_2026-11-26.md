# Seed lane gate diverts any source containing the text `window_winit` to the interpreter

- **Date:** 2026-11-26
- **Status:** OPEN
- **Area:** Rust seed driver, `src/compiler_rust/driver/src/exec_core.rs`
  (`source_uses_jit_unsafe_graphics_runtime`)
- **Split out of:** `module_load_24s_unless_window_winit_imported_2026-07-25.md`, which asked
  twice (2026-11-05, 2026-11-25) for this to get its own record.

## Defect

`source_uses_jit_unsafe_graphics_runtime` returns `source.contains("window_winit")` on the raw
entry-file text. Any mention, including a comment, sends the whole program to the tree-walk
interpreter. Lane choice therefore depends on comment text, not on what the program imports or
calls, and the 2D startup timings people compare are lane timings in disguise.

## Evidence (2026-11-26, Linux aarch64 NVIDIA GB10, seed sha256 prefix `fb80903917d6d5f5`)

Same `fn main() -> i64: print "ok"; 0` body, `SIMPLE_NO_DEPRECATED_WARNINGS=1 seed run`,
rounds 2-5 (round 1 is the first run of the session):

| entry file | lane | wall |
|---|---|---|
| `use std.gpu.engine2d.engine` | JIT | 2.23-2.88 s (first run 6.48 s) |
| same + `use std.io.window_winit.{winit_loop_new}` | interpreter | 0.56-0.77 s |
| same as row 1 + a `# window_winit` comment line | interpreter | 0.54-0.72 s |
| no imports | JIT | 0.04-0.05 s |

Rows 1 and 3 differ only in a comment, and the comment makes the program about 4x faster to start.

## Fix direction

Decide the lane from the resolved import closure, or from an explicit attribute or env knob, not
from a substring of the entry text. Keep `SIMPLE_EXECUTION_MODE=interpreter` as the escape hatch.

Lane attribution check: the engine-only file under `SIMPLE_EXECUTION_MODE=interpret` takes
0.47-0.79 s, the same as the substring-diverted rows. JIT with an empty `HOME` takes 1.50-1.54 s.
