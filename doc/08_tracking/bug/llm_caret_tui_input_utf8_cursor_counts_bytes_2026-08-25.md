# TUI input widget: multibyte insert advances cursor by BYTES and corrupts the value — 2026-08-25

Status: FIXED 2026-08-25 (uncommitted at time of writing) — defect in
`src/lib/nogc_sync_mut/tui/widgets/input.spl` (std), surfaced by the
llm_caret decoder spec. See "Fix" and "Evidence" below.

## Symptom

`test/01_unit/app/llm_caret/chat_tui_input_spec.spl` —
`Results: 22 total, 18 passed, 4 failed` (fresh seed from origin/main
`684fadabcae`):

```
✗ should insert valid two three and four byte code points
    expected (���, 9) to equal (¢한😀, 3)
✗ should accept the valid Unicode scalar boundary sequences
    expected (�������, 21) to equal (�������, 7)
✗ should insert a decoded Unicode code point at the widget cursor
    expected (A�B, 4) to equal (A한B, 2)
✗ should preserve ANSI navigation around decoded Unicode input
    expected (>��!, 8) to equal (>¢😀!, 4)
```

## Root cause

The byte-at-a-time decoder in `src/app/llm_caret/tui_input.spl:101-165` is
correct: it emits one completed code point per sequence
(`_utf8_emit_or_reject`). `apply_raw_key_decode` (`tui_input.spl:167-178`)
then calls `input_insert_char(input, char_from_code(cp))`, and
`src/lib/nogc_sync_mut/tui/widgets/input.spl:98-106` does

```
val before = widget.value.substring(0, widget.cursor_pos)
val after  = widget.value.substring(widget.cursor_pos, len(widget.value))
...
cursor_pos: widget.cursor_pos + len(ch),
```

`len()` is a BYTE count by contract
(`test/01_unit/lib/common/text_byte_len_vs_codepoint_index_spec.spl`:
"`text.len()` / `text.length()` are BYTE counts, while `char_at(i)` … are
CODEPOINT-indexed"), so the cursor advances 2/3/4 per code point (hence 9 for
three code points) while `substring` slices by code point, and the next insert
splits the buffer mid-sequence — the replacement characters above. Same defect
class as `doc/08_tracking/bug/text_byte_len_vs_codepoint_index_family_2026-08-06.md`.

Minimal repro on the fresh seed: `char_from_code(0xA2)` equals `"¢"` but
`.len()` is 2; `"¢".len()` is 2.

## Unblock condition

`input_insert_char` (and the sibling delete/move helpers in the same widget)
must advance/measure in code points (`+ 1` per inserted code point, or a
codepoint-length helper), keeping `substring` semantics. Re-verify with
`bin/simple test test/01_unit/app/llm_caret/chat_tui_input_spec.spl`.

## Root-cause correction (2026-08-25)

The "substring is codepoint-indexed" premise above is wrong on the test
engine: probed on both the shared seed (2026-08-23) and a fresh origin seed
(2026-08-25), `"¢".substring(0, 1)` is `�` and `"¢".substring(0, 2)` is `¢`,
i.e. `substring` and `len` are BOTH byte-based, while `chars()` /
`char_at` are codepoint-based (the stdlib says so itself:
`src/lib/common/text.spl:26-28`). The real defect is that `cursor_pos` was a
byte offset while the widget's public contract (and its consumers,
`chat_tui_input_spec`) treat it as a codepoint index — and a first attempt
that merely counted codepoints for the cursor but kept `substring(0,
cursor_pos)` split `¢` mid-sequence (`expected (�😀, 3) to equal (¢한😀, 3)`).

## Fix

`src/lib/nogc_sync_mut/tui/widgets/input.spl`:
- `input_text_len(s)` — codepoint length (`s.chars().len()`), used for the
  cursor bound in `make_input_widget_with_value`, `input_delete_forward`,
  `input_move_right`, `input_move_end`, and `+ input_text_len(ch)` on insert.
- `input_byte_offset(s, cp_index)` — converts the codepoint cursor to the
  byte offset `substring` needs; used by `input_insert_char`,
  `input_delete_back`, `input_delete_forward`, and the `input_render` scroll
  start. `cursor_pos` is now a codepoint index everywhere.
- `input_render`: `result = result + [x]` in loops -> `result.push(x)`
  (COLL001 lint error on the changed file; semantics identical).

Reproduce + generalization specs (both mirrors kept identical):
`test/01_unit/lib/nogc_async_mut/tui/widgets/tui_widgets_facade_spec.spl`
and `test/unit/lib/nogc_async_mut/tui/widgets/tui_widgets_facade_spec.spl`,
describe `input widget cursor arithmetic is codepoint based`: insert
2/3/4-byte code points, backspace over a 4-byte emoji, cursor-left across a
3-byte hangul, insert/delete-forward in the middle of multibyte text, ASCII
regression.

## Evidence

Widget spec, BEFORE (both trees): `Results: 6 total, 2 passed, 4 failed` —
`expected (¢한😀, 9) to equal (¢한😀, 3)`, `expected (a�b, 4) to equal (ab, 1)`,
`expected 3 to equal 0`, `expected 16 to equal 2`.
Widget spec, AFTER (shared tree AND clean origin worktree
`/mnt/data/tmp/claude-1000/caret-clean` @ `684fadabcae`):
`Results: 6 total, 6 passed, 0 failed`.

`chat_tui_input_spec.spl`: BEFORE `Results: 22 total, 18 passed, 4 failed`
(the four listed above) -> AFTER `Results: 22 total, 22 passed, 0 failed` on
the shared tree at 04:0x; later runs on BOTH trees give `Results: 22 total,
19 passed, 3 failed` — the residual below, which is not the widget.
`chat_tui_runtime_spec.spl`: `Results: 20 total, 20 passed, 0 failed` (both
trees).
`chat_tui_spec.spl` (clean tree): `Results: 62 total, 62 passed, 0 failed`
before and after.
`bin/simple lint src/lib/nogc_sync_mut/tui/widgets/input.spl`: `Found 0
error(s), 4 warning(s)` (warnings pre-existing, `unnamed_duplicate_typed_args`
in the docstring example).

### Second defect (FIXED 2026-08-25): `char_from_code` shadowed by `encoding/utf8.spl`

The 3 examples that stay RED after the widget fix have the CURSOR right and
only the VALUE corrupt: `expected (���, 3) to equal (¢한😀, 3)`, `(A�B, 2)`,
`(>��!, 4)`. Each `�` is U+FFFD (3 bytes). Probe under `bin/simple test` with
`app.llm_caret.chat_tui` imported: `char_from_code(162)` returns `�` (len 3,
1 codepoint) — the SAME call in a spec that imports only `std.string_core`
returns `¢` (len 2), and `bin/simple run` of the exact
`decode_raw_key_byte` -> `apply_raw_key_decode` sequence prints
`step|¢한😀|3|`. `src/lib/common/encoding/utf8.spl:366` defines a second
`fn char_from_code(code: i64) -> text` that returns `"�"` for every
`code >= 128`; `app.llm_caret.chat.spl` pulls `encoding.utf8` in, and under
the interpreter's flat function namespace that definition wins over
`std.string_core.char_from_code` (`tui_input.spl:13`), so the widget is
handed U+FFFD before it ever runs. Which definition wins depends on module
load order — a parallel session's edits to `src/lib/common/json/*` and
`src/app/llm_caret/json_helpers.spl` flipped the shared tree from 22/22 to
19/3 with the widget file byte-identical. Widget spec (literal `¢한😀`) is
6/6 on both trees.

**Fix** (`src/lib/common/encoding/utf8.spl`): `char_from_code` now delegates
every code >= 128 to `char_from_codepoint` (-> `utf8_encode_one` ->
`rt_bytes_to_text`), so both definitions produce byte-identical UTF-8 for
every valid scalar 0..0x10FFFF; neither definition was deleted and no app
import changed. `char_from_codepoint` gained a `cp >= 0` guard on its ASCII
fast path (it delegates back to `char_from_code`, which recursed forever on
negative input — caught by the new spec: `stack overflow: recursion depth
1000 exceeded`). Policy difference kept and asserted: invalid input
(surrogates, > U+10FFFF, negative) is U+FFFD here (utf8_encode_one policy)
but `""` in string_core (its documented policy); the llm_caret decoder never
emits those. Spec: `test/01_unit/lib/common/encoding/utf8_spec.spl`,
describe `char_from_code encodes scalars above 127` (test/unit mirror already
diverged and baselined, left alone). BEFORE: `Results: 52 total, 49 passed,
3 failed` (`expected 3 to equal 2` — len of `char_from_code(0xA2)`). AFTER:
`Results: 52 total, 52 passed, 0 failed` on both trees;
`chat_tui_input_spec.spl` `Results: 22 total, 22 passed, 0 failed` on both
trees; `chat_tui_runtime_spec.spl` 20/20; `chat_tui_spec.spl` 62/62 (clean);
`bin/simple lint src/lib/common/encoding/utf8.spl`: 0 errors (17 pre-existing
warnings).

## FIXED-IN-SEED-SOURCE (pending redeploy) — 2026-08-25 (module,name)-keyed registry

The underlying name-keyed co-compile registry defect is FIXED IN SEED SOURCE
(not yet deployed; built binary sha256
27f4e599f3e4f48d637ff53f7691c2d4660be0c84e17ba35b508a811d12c734f from a clean
origin/main (54b8cef2700) worktree at /mnt/data/tmp/claude-1000/caret-clean).

Mechanism fixed, per lane:
- Interpreter (interpreter_call/mod.rs `filter_overloads_by_caller_binding`):
  bare-name overload candidates are pre-filtered through the CALLING module —
  its own definitions, then its `__simple_flatten_import_binding__=` bindings
  (facade/`export use` chains followed, glob sources included), before any
  arity/type scoring. Top-level entry statements execute under the "<entry>"
  owner (interpreter_eval.rs guard) so spec `it`-block lambdas inherit it.
- Cranelift JIT (hir/lower): a bare name defined by 2+ DISTINCT owners keeps
  the FIRST owner's definition bare and emits every LATER owner's definition
  under `flatten_owner_mangled_name(owner, name)`; call sites are rewritten
  per caller (`resolve_duplicate_fn_symbol`: own module, import binding,
  unique glob source). Two glob sources both providing the name is a hard
  error in both lanes.
- Pure-Simple mirror (src/compiler/10.frontend/core/interpreter):
  `func_table_register_owned` (module_loader_core) + per-importer
  `func_import_binding_register` (eval_decls DECL_USE) +
  `func_resolve_for_caller` consulted in eval_calls before the flat table.
  Spec: test/01_unit/compiler/interpreter/cross_module_owned_fn_resolution_spec.spl (5/5).

Deviation from the intended hard error: a no-route caller (neither defines
nor imports the name) falls back to the historical first-registered pick with
a warn-once, NOT a fatal error — the 350-symbol same-signature sync/async
mirror family (e.g. `step`) is reachable from virtually every spec and a
fatal diagnostic measured type_domain_resolver_spec at 0/4. Promote to fatal
once the mirror family is namespaced.

Evidence (all on sha 27f4e599..., clean worktree): 3-file repro prints "a" on
both engines in BOTH import orders with engine receipts; sabotage replays of
both real incidents pass (json_helpers_spec 45/45 with the
`use std.mcp.helpers.{...}` import reinstated; chat_tui_input_spec 22/22 with
the old utf8 `char_from_code` U+FFFD stub reinstated);
cross_module_symbol_collision_spec 2/2 with SIMPLE_BIN pointed at the new
seed (JIT arm was RED by design before); module_resolver/resolution battery
green at baseline; Rust unit tests
pipeline::module_loader::duplicate_fn_resolution_tests 2/2.
