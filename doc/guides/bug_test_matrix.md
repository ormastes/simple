# Bug-Oriented System Test Ideas

Scenarios likely to break the current implementation; prioritize as new system tests that assert failures until fixed.

- `match` in CLI executable path (both `=>` and `case …:`), with and without guards — currently errors with “undefined variable”.
- `match` in CLI when reading `main.spl` from disk (not `-c`), same syntax variants — same “undefined variable” failure.
- `match` with guards that bind names (`case n if n > 0:`) — binding seems lost before guard evaluation.
- Mixed `case`/`=>` arms in one `match` — parser accepts, executable path likely still fails.
- `match` inside functions run via CLI (`fn f(x): match x: …`) — executable path may drop bindings similar to top-level.
- `match` on enums in CLI executable path (e.g., `Status::Ok => main = 1`) — validate variant binding and payloads.
- `match` with pattern destructuring (tuples/arrays/structs) in CLI executable path — ensure bindings survive codegen path.
- Trailing-block (`case pat:`) with multi-statement body in CLI executable path — confirm indentation handling.
- Guards that reference previously bound names from outer scope (`let y = 2; match x: case y:`) — shadowing could miscompile.
- Cross-file import plus `match` in imported module (CLI `main.spl` importing `lib.spl`) — ensure dependency tracking keeps symbols.
