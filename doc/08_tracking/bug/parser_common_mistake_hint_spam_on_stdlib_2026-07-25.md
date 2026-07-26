# Parser emits ~11.5k false-positive `PythonSelf` hints on our own stdlib (150k log lines, ~5 s per run)

- **Date:** 2026-07-25
- **Area:** `src/compiler_rust/parser/` (hint classification) +
  `src/compiler_rust/compiler/src/pipeline/module_loader.rs` (hint printer)
- **Severity:** medium — not a correctness bug, but it buries every real
  diagnostic and costs ~16% of a short interpreted run.
- **Status:** **STILL OPEN** — the false positives themselves are not fixed. The
  printer's O(hints x file-lines) cost was fixed 2026-07-26; see "Partial work
  landed" at the end. Found while root-causing the 2D × headless showcase cell
  (see `engine2d_load_font_interpreter_3kb_per_sec_2026-07-25.md`).

## What happens

Any interpreted run that imports `std.gpu.engine2d.engine` emits a wall of
diagnostics before doing any work. Measured on linux-x86_64:

| run | log lines | log bytes |
|---|---|---|
| `probe_b_render.spl` (import Engine2D, draw 2 shapes at 320x240) | **150,160** | 5,223,522 |
| `graphics_2d_showcase.spl` @ 320x240, killed at 60 s | 75,143 | 2,615,255 |

Line-shape histogram of the showcase log (digits normalized to `N`):

```
5763  info: Common mistake detected: See error message for details
5763  In Simple, 'self' is implicit in methods. Don't write 'self.'.
5763  Python:  self.x = value
5763  Simple:  x = value     # self is implicit in methods
5784     |
```

`probe_b_render.spl` alone produces **11,518** `Common mistake detected` blocks.

## Why it is a false positive

`CommonMistake::PythonSelf` is classified as an info-level hint. Grep marker,
present in **both** `src/compiler_rust/parser/src/parser_impl/core.rs` and
`src/compiler_rust/parser/src/parser_helpers.rs`:

```rust
CommonMistake::TsLet | CommonMistake::PythonSelf | CommonMistake::RustFnMut => ErrorHintLevel::Info,
```

and the message itself, `format!("Common mistake detected: {}", mistake.suggestion())`.

It fires on every `self.` field access. But the stdlib uses `self.field`
legitimately and pervasively — e.g. in
`src/lib/gc_async_mut/gpu/engine2d/engine.spl`:

```
val owner: Engine2DFontOwner = self.font_owner
```

and in `src/lib/nogc_sync_mut/concurrent/thread.spl`:

```
rt_thread_id(self.handle)
```

These compile and run correctly. The heuristic is a Python-migration hint being
applied to first-party code that is not migrating from Python, so it is ~100%
false-positive volume on our own tree.

## Cost

Suppressing the hints with the existing gate (grep marker
`SIMPLE_NO_DEPRECATED_WARNINGS` / `SIMPLE_ALLOW_DEPRECATED` in
`fn display_parser_hints`, `src/compiler_rust/compiler/src/pipeline/module_loader.rs`)
on the identical workload:

| | wall time | log lines |
|---|---|---|
| `probe_b_render.spl` default | 31 s | 150,160 |
| `probe_b_render.spl` with hints suppressed | **26 s** | **7** |

So the diagnostic spam costs **~5 s (~16%)** of a 31 s run, and hides the
7 lines that actually matter. It is a real but secondary contributor — it is
*not* what makes the 2D showcase cell fail (that is `load_font`).

## Contributing implementation defect: O(hints x file lines) printer

`display_parser_hints` re-scans the source from the top for every hint. Grep
marker in `src/compiler_rust/compiler/src/pipeline/module_loader.rs`:

```rust
if let Some(line) = source.lines().nth(hint.span.line - 1) {
```

`lines().nth(n)` is O(n). With ~11.5k hints spread over large files this is
quadratic in file length. Even when the hints are legitimate, the printer should
build the line index once per file rather than per hint.

## Proposed fix

1. **Do not raise `PythonSelf` for `self.<ident>` field access at all** — that
   form is valid Simple. Restrict the heuristic to the actual Python shape it
   was written for (`def f(self, ...)` parameter lists).
2. **Hoist the line index** in `display_parser_hints` out of the per-hint loop.
3. Optionally cap repeated identical hints per file ("... and N more").

Per `.claude/rules/code-style.md` these are hint *emissions*, not dead code —
the fix is to correct the classification and gate the volume, not to delete the
diagnostic.

## Reproduce

```bash
# noisy
bin/simple run <any .spl importing std.gpu.engine2d.engine>   # ~150k lines
# quiet + ~16% faster
SIMPLE_NO_DEPRECATED_WARNINGS=1 bin/simple run <same file>    # 7 lines
```

## Partial work landed 2026-07-26 — printer cost, NOT the false positives

The agent working this was cut off partway. What landed is real but does not
close the bug:

1. **`display_parser_hints` was O(hints x file-lines).** It called
   `source.lines().nth(hint.span.line - 1)` per hint, re-walking the file from
   byte 0 every time. With ~11.5k hints on a large stdlib file that is quadratic.
   The source is now indexed into a `Vec<&str>` once.
2. **Underflow hardening.** The same expression computed `hint.span.line - 1` on
   a `usize`, so a hint reported at line 0 would panic. Now `checked_sub`.
3. **Duplicated severity classification unified.** `parser_impl::core` (initial
   token) and `parser_helpers::advance` (every subsequent token) carried
   byte-identical 40-line `match` blocks mapping `CommonMistake` to
   `ErrorHintLevel`. Both now call one `CommonMistake::hint_level()`. Behaviour
   is unchanged — this removes a silent-divergence hazard, it does not alter any
   severity.

Verified: `cargo check -p simple-parser -p simple-compiler` rc=0 with no new
warnings; `cargo test -p simple-parser` 236 + 20 further suites, **0 failed**.

**What is still broken.** The false positives are undiminished and the message
is still content-free. A 17-line probe importing `std.common.encoding.font_registry`
emits 41 copies of:

```
info: Common mistake detected: See error message for details
See error message for details
```

Two defects remain: the `PythonSelf`-class detection fires on valid Simple, and
the hint carries no actionable text (`_ => "See error message for details"` in
`CommonMistake::message`), so even a true positive would be unactionable. Both
are untouched.

**Not verifiable against a deployed binary.** These are Rust-seed parser
changes; the shipped `bin/simple` still contains the old code. The evidence
above is a source-level build and test, not a redeploy — no deploy was made.
