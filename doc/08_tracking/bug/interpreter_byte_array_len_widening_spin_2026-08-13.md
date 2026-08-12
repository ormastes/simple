# Interpreter byte-array `.len()` widening spin + JIT `.bytes()` leaf misbinding (2026-08-13)

Status: FIXED — `len`/`is_empty` packed fast path added in
`src/compiler_rust/compiler/src/interpreter_method/collections.rs`; the
`compile_call` `.bytes()` special case in
`src/compiler_rust/compiler/src/codegen/instr/calls.rs` reverted.
Verified: `widget_draw_ir_widgets_spec` 10/10 (31s, previously timed out at
300s), event specs 4/4, `vulkan_api_drawir_readback_spec` PASS,
`web_css_essentials_spec` PASS.

## Symptom

After the 2026-08-12 async/mimalloc batch (`c6c5eb2b`), any BDD spec whose
module also exercises the widget/font pipeline (e.g.
`test/01_unit/lib/common/ui/widget_draw_ir_widgets_spec.spl`) burned 100% CPU
indefinitely and was killed at its timeout budget. JIT-compiled runs of the
same workload were unaffected (2-3s). The spec modules run interpreted
because `describe`/`it` blocks create closures, which the JIT correctly
refuses (jit.rs Defect-1/Defect-2 guards).

## Bisection

Seed bisect over `254399a8..c6c5eb2b` (v11 repro: empty `it` + one-button
`widget_tree_to_draw_ir_cpu` walk):

- `354b8a58ed` GOOD (1.7s) -> `acc98a764a` BAD (60s+, 100% CPU). Reverting
  only the `calls.rs` hunk at `acc98a764a` made it GOOD.
- Current tree with the `calls.rs` revert still spun; gdb interrupt placed
  the spin in `interpreter_method::collections::handle_byte_array_methods`
  doing `byte_array_values` alloc/drop churn.

## Root cause 1 (JIT): `.bytes()` leaf special case over-fires

`acc98a764a` added an `exact_string_bytes_runtime` shortcut in
`compile_call`: any call whose name leaf is `bytes` with exactly one
STRING-typed argument is routed to `rt_string_bytes`, bypassing normal
user-function resolution. In font/walk module closures this misbinds calls
that should have resolved to user functions, producing garbage values and a
100% CPU spin in the generated code. Reverted to the pre-`acc98a764a`
resolution (`sffi_alias_target` fallback chain). The original intent
(fail-safe for hand-built/legacy MIR that retains only the leaf) needs a
narrower predicate and a regression test before re-landing.

## Root cause 2 (interpreter): metadata ops widen the whole blob

The same commit introduced `handle_byte_array_methods`, which routes EVERY
byte-array method through `Value::byte_array_values(bytes)` — one `Value`
per byte — before dispatching to the generic array kernel. That includes
`.len()` and `.is_empty()`, which only need the blob's length. The font
loader (`resolve_font_metrics_with_language` -> sfnt measure) calls `.len()`
on a ~1.7MB TTF blob per glyph-table probe: a `SIMPLE_TRACE_BIG_BYTEARRAY=1`
receipt counted **1390 `.len()` calls on the 1,708,408-byte blob in 25s**,
i.e. ~2.4 billion `Value` allocations for what is 1390 integer reads. That
is the spin: finite but effectively unbounded.

Fix: packed fast path in `handle_byte_array_methods` — `len`/`length` and
`is_empty` with no args return directly from the packed slice without
widening. `SIMPLE_TRACE_BIG_BYTEARRAY=1` env-gated receipt retained to trace
any future >1MB widening.

## Not the cause (checked and cleared)

- `3d15d0703a` "reject raw heap transport" and the later transfer-hardening
  commits (`3ea77d992d`, `38f34608cb`, `d8f457194a`): an earlier bisect step
  fingered `3d15d0703a`, but that step still contained the widening defect.
  With only the `len` fast path added and the hardening fully intact, v11
  passes in 1.6s. The channel/actor/clone fail-closed semantics are
  unchanged in this tree.

## Repro artifacts

- `/tmp/wp_v11.spl`-style: `describe` + empty `it`, then build a one-button
  tree and call `widget_tree_to_draw_ir_cpu` — spun before, 1.6s after.
- `SIMPLE_TRACE_BIG_BYTEARRAY=1 simple run <prog>` prints
  `[bigba] method=<m> len=<n>` for byte-array method calls on >1MB blobs.
