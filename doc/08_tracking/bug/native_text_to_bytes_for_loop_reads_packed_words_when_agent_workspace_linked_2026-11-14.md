# Native: `for b in text_to_bytes(s)` yields packed 8-byte words once `app.llm_caret.agent_workspace` is in the unit

Status: verification-pending
Severity: P1 (native-only wrong result, silent)

## Root cause (2026-11-14, lane `work/caret-native-defects-20261114`)

Not the two same-signature `text_to_bytes` definitions. A dependency's
PRIVATE function alias leaked into the importing module.

`materialize_import_aliases`
(`src/compiler_rust/compiler/src/hir/lower/import_loader.rs`) guarded only the
`globals` row with `dependency_import_depth == 0`; `method_return_types`,
`declared_function_returns`, the function-alias map,
`imported_function_names`, `imported_function_value_types`, `extern_fn_names`
and `pure_functions` were written under the bare alias name at every depth.
Several modules in the `agent_workspace` closure do
`use std.common.crypto.types.{crypto_text_to_bytes as text_to_bytes}` (a
`[i64]` function), so the lowered module's own, explicitly imported
`text_to_bytes` was retyped. Instrumented seed, call site in the probe:

```
name=text_to_bytes ... mrt=Array { element: TypeId(5) /*i64*/ } globals=Array { element: TypeId(6) /*u8*/ }
```

The call still bound the real `[u8]` function, but the for-loop / index read
was lowered as `rt_typed_words_i64_at` over a packed byte buffer.

Four-module repro (no llm_caret):

```simple
use std.common.string_core.{text_to_bytes}
use std.common.crypto.constant_time.{black_box}   # privately aliases crypto_text_to_bytes as text_to_bytes

fn main() -> i64:
    for b in text_to_bytes("a-1"):
        print "loop=" + b.to_i64().to_text()
    0
```

Seed-tip `97728d94d5f`: `loop=3222881 / loop=0 / loop=0`.

Fix: a dependency-depth alias publishes nothing but its type-level alias
(which its own signatures need). Tests:
`hir/lower/tests/fn_alias_import_scope_tests.rs` (both import orders, RED
`["rt_typed_words_i64_at"]` -> GREEN `["rt_typed_bytes_u8_at"]`) and
`test/01_unit/compiler/dependency_fn_alias_return_type_native_spec.spl`.

Not covered: a dependency's NON-aliased same-named function still overwrites
the bare-name return type last-wins (`Node::Function` arm, no owner claim like
`claim_imported_enum_name`). Harmless here because both `text_to_bytes`
definitions return `[u8]`; it is the family behind the `join_path` "2
co-compiled definitions with 2 differing signatures" warning.
Found: 2026-11-14, lane `work/caret-native-knob-20261114`
Seed: `/c/dev/wt/seed-tip/simple.exe`, build-commit `97728d94d5f11890bac2e0a5e8d41ce65139047b`
Host: Windows 11, llvm-mingw 20260922 UCRT, `SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_NATIVE_INCREMENTAL=1`

## Symptom

Native `llm_caret.exe workspace <id> attach agent-1` exits 1 with
`error invalid_name agent-1`. The interpreter accepts the same name.
`_valid_name` (`src/app/llm_caret/agent_workspace.spl:403`) iterates
`text_to_bytes(name)` and sees garbage instead of byte values, so every name is
rejected on the smux backend.

Visible in the suite as the native-mode failure of
`test/03_system/app/llm_caret/workspace_cli_system_spec.spl`
("attaches three agents, isolates their worktrees, broadcasts, and tears down"):

```
expected 1 to equal 0
expected error invalid_name agent-1
 to contain window cli-team:agent-1
```

Run with `LLM_CARET_NATIVE_BIN=<native llm_caret.exe>`:
`Results: 4 total, 3 passed, 1 failed`. Interpreted: `4 total, 4 passed, 0 failed`.

## Minimal repro

`probe.spl`:

```simple
use std.common.string_core.{text_to_bytes}
use app.llm_caret.agent_workspace.{workspace_backend, window_open, agent_workspace}

fn main() -> i64:
    for b in text_to_bytes("a-1"):
        print "byte=" + b.to_i64().to_text()
    print "backend=" + workspace_backend()
    val r = window_open(agent_workspace("probe-x", ".", ""), "bad name!", ".", "")
    print "bad=" + r.status + " " + r.reason
    0
```

```
$SEED native-build probe.spl -o probe.exe --cache-dir build/nb/cache && ./probe.exe
```

Native output (462 modules compiled):

```
byte=3222881
byte=-9223366535643127486
byte=0
```

`3222881 == 0x312D61`, i.e. the three bytes `a - 1` read as ONE little-endian
8-byte word: the loop makes 3 iterations (length is right) but loads each
element with an 8-byte stride from a packed `[u8]` buffer.

Control 1 - same file without the `agent_workspace` import (3 modules compiled),
native: `byte=97 / byte=45 / byte=49` (correct).
Control 2 - either file under `$SEED run`: `97 / 45 / 49` (correct).

So the defect is not in `text_to_bytes` itself; it depends on what else is
co-compiled. Not yet isolated which module flips it.

## Leads (unverified)

- Two public `text_to_bytes(s: text) -> [u8]` definitions exist:
  `src/lib/common/text_bytes.spl:31` (re-exported by
  `src/lib/common/string_core.spl:496`, returns the packed `rt_text_to_bytes`
  array) and `src/lib/common/base_encoding.spl:85` (builds `var out: [u8] = []`).
  If the large unit resolves the call to one definition but types the loop
  element from the other (or loses the `[u8]` element type on a `$dupN`
  variant), the 8-byte stride follows.
- Possibly related: `core_string_bytes_word_slot_tag_mismatch_2026-10-05.md`,
  `byte_span_cross_module_misread_2026-07-19.md`.

## Unblock condition

The repro prints `97 / 45 / 49` natively (met), and
`workspace_cli_system_spec.spl` passes 4/4 with `LLM_CARET_NATIVE_BIN` set.
No caret-side workaround was applied.

Update 2026-11-14: `attach agent-1` no longer returns `invalid_name` natively,
but the spec is still 3/4 for a different reason, filed as
`native_llm_caret_smux_owner_spawned_as_interpreter_of_itself_2026-11-14.md`.
