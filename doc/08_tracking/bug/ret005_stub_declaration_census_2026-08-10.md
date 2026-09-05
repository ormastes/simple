# RET005 stub-declaration census: 46 sites, zero live lies

- **Date:** 2026-08-10
- **Status:** TRIAGED — no production defect found in this category
- **Rule:** `src/compiler/35.semantics/lint/return_type_mismatch.spl` (code `RET005`)
- **Scope:** owned `.spl` under `src/` (vendored trees excluded), plus `test/`,
  `scripts/`, `tools/`

## Headline

The circulated figure was "roughly 50". The real count is **46** in `src/`
(plus 1 unique site in `test/feature/usage`, double-counted as 2 because
`test/03_system/` is a byte-duplicate tree). Of those 46:

| class | count | share |
|-------|------:|------:|
| LEGITIMATE — trait / abstract method declaration | 10 | 22% |
| LEGITIMATE — `@extern` SFFI declaration body | 15 | 33% |
| UNWIRED — no callers outside its own layer | 21 | 46% |
| **LIVE LIE** | **0** | 0% |

**No RET005 site is a live lie.** Every hit is a declaration whose body is a
placeholder *by construction* (trait signature, `@extern` binding) or lives in a
file nothing calls. This category is materially different from the three
"unconditional not-found" string primitives that motivated the sweep: those had
real production callers; none of these do.

## How the count was derived

`RET005` fires when a `fn`/`me` declares a *scored* value return type
(`bool` / integer / float / `text` / `[T]` — Option, Result, generics and user
types are deliberately unscored) and the **last top-level statement of its
body** is a placeholder: `pass`, `...`, `todo()`, `pass_todo`, `pass_dn`,
`pass_do_nothing`.

Two independent derivations:

1. **Faithful reimplementation** of the rule's algorithm (signature joining,
   indent-scoped body extent, nested-fn skipping, triple-quote masking) run over
   all 14,337 non-vendored `.spl` files → **46**.
2. **Narrow structural grep** for the single-line-signature / whole-body-is-one-
   stub shape → **28**, a strict subset of (1), with 3 extra hits at
   `src/compiler/70.backend/linker/smf_reader.spl:105,110,115` that are *not*
   RET005: there the `pass_todo` is the FIRST body line and the tail expression
   is `[]`. Those three are already filed as
   `doc/08_tracking/bug/smf_reader_bridge_silent_nil.md`.

The rule's own census driver
(`scripts/check/census-return-type-mismatch.spl`) passes its planted-violation
selftest (`control: 5 planted violations detected, 13 correct forms silent`) but
**cannot complete a full `src/` scan**: it drops to the interpreter
(`[jit-fallback] unresolved external symbol 'rt_file_is_char_device': whole
module dropped to the interpreter`) and is then killed by
`kill_simple_monitor`, even with `SIMPLE_TIMEOUT_SECONDS=0` (the env var does
not reach the monitor). That is a separate, real gap: **the census the
"warn → census → error" promotion depends on cannot actually be produced by the
shipped tool.** Filed below.

## Classified sites

### UNWIRED (21)

| site | count | evidence |
|------|------:|----------|
| `src/compiler/90.tools/ffi_gen/specs/im_rs.spl` — all 20 `im_hashmap_*` / `im_vector_*` / `im_hashset_*` | 20 | `pass_todo("Rust FFI bridge not built")`. Exhaustive `/usr/bin/grep -rn` over `src/ test/ scripts/` for `im_hashmap_new`, `im_vector_new`, `im_hashset_new` returns **zero** hits outside the file. It is an SFFI *spec* input for the generator, not a callable API. |
| `src/compiler_rust/lib/std/src/tooling/dashboard/collectors/vcs_collector.spl:83` `_rt_execute_command` | 1 | See note below — genuinely broken, but unreachable. |

**`vcs_collector` note (latent, not live).** `execute_command` (line 78) binds
`@extern("runtime", "rt_execute_command")`, and `rt_execute_command` is
registered in **no** runtime — `/usr/bin/grep -rn rt_execute_command` over all
`.c`/`.rs`/`.h` finds only this declaration. It therefore returns a silent nil,
so all five callers (`vcs_collector.spl:46,52,58,64,70`, the `jj log` / `jj
status` probes) would report empty VCS state rather than failing. This is
exactly the pattern the sibling comment in
`src/compiler_rust/lib/std/src/tooling/todo_parser.spl:418` records for the
deleted `rt_path_exists` binding. It is **not** a live lie only because nothing
reaches it: `collect_vcs_state` is imported solely by
`src/compiler_rust/lib/std/src/tooling/dashboard/collector.spl:13`, which has no
importers; the shipped dashboard uses
`src/app/dashboard/dashboard_collectors` instead. Per the task scope the wiring
was deliberately **not** built. The correct resolution is to delete this
collector or point it at a real process-run symbol — not to add a caller.

### LEGITIMATE — trait / abstract method declarations (10)

A trait method with no default is written `pass` in this language; the
implementations carry the behaviour.

| site | lines | implementers |
|------|-------|--------------|
| `src/compiler/70.backend/backend/common/type_mapper.spl` `map_primitive`/`map_pointer`/`backend_name` | 33, 40, 44 | `c_type_mapper.spl:42`, `cranelift_type_mapper.spl:47`, … — explicitly marked `# === Abstract methods (must implement) ===` |
| `src/compiler/95.interp/execution/mod.spl` `compile`/`execute`/`has_function`/`backend_name` | 24, 26, 28, 30 | `trait ExecutionManager` (line 21); `class LocalExecutionManager` (line 48) defines all four for real at 71/79/84/88 |
| `src/compiler/70.backend/linker/obj_taker.spl` `path`/`read_note_sdn` | 741, 749 | `trait SmfReader`; implemented by `smf_reader.spl` / `_SmfReaderMemory` |
| `src/compiler_rust/lib/std/src/context_manager.spl` `__exit__` | 37 | `trait ContextManager` protocol declaration; the live implementations are `src/lib/nogc_sync_mut/src/core/context_manager.spl:54,144` |

### LEGITIMATE — `@extern` SFFI declaration bodies (15)

An `@extern`-annotated `fn` binds a native symbol; `pass` is the required
placeholder body and the declared return type is the native signature.

| site | lines |
|------|-------|
| `src/compiler_rust/lib/std/src/bare/mem.spl` `read_u8/16/32/64`, `volatile_read_u8/16/32`, `compare` | 8, 12, 16, 20, 41, 45, 49, 79 |
| `src/compiler_rust/lib/std/src/bare/time.spl` `cycles`, `micros`, `millis`, `ticks`, `ticks_per_second` | 8, 12, 16, 33, 38 |
| `src/compiler_rust/lib/std/src/bare/startup.spl` `interrupts_enabled` | 56 |
| `src/compiler_rust/lib/std/src/tooling/todo_parser.spl` `_rt_file_read_text` | 414 — target symbol **does** exist (`src/runtime/runtime.c:1445`, `runtime_native.c:7570`) |

## Rule fix landed with this triage

`rtm_is_stub_body` tested `s.starts_with("pass_")` as a bare prefix, so any
expression whose first token merely begins with those five characters was
reported as a placeholder. Measured false positives (3, all correct code):

- `src/compiler/60.mir_opt/mir_opt/mod.spl:55` — `pass_name == "inline_small_functions" or …`
- `src/compiler/60.mir_opt/mir_opt/mod.spl:582` — `pass_name == "typed_byte_canon"`
- `src/lib/nogc_sync_mut/engine/render/graph_ir3d.spl:83` — `pass_id`

The reserved no-op words are exactly `pass_todo`, `pass_dn`, `pass_do_nothing`
(1270 / 715 / 103 uses); `pass_name`, `pass_count`, `pass_id`, … are ordinary
identifiers. The check now matches only the reserved word, and only when the
token ends there or opens an argument list. Loose rule: 49 findings. Tightened
rule: 46. Every one of the 3 removed is verified correct code.

## Open follow-ups (not fixed here)

1. **The census driver cannot produce a census.** `bin/simple run
   scripts/check/census-return-type-mismatch.spl --list src` never finishes: the
   unresolved `rt_file_is_char_device` extern drops the whole module to the
   interpreter, and `kill_simple_monitor` then SIGTERMs it. Until that symbol is
   resolved (or the driver is compiled), the "warn → census → error" promotion
   in `doc/08_tracking/bug/declared_return_type_not_enforced_2026-08-09.md`
   cannot be driven by its own tool. Numbers in this document came from an
   independent reimplementation for that reason.
2. **`rt_execute_command` binds nothing** (`vcs_collector.spl:81`). Delete the
   collector or re-point it; do not wire a caller to it as-is.
3. **`im_rs.spl` is a 20-function API that nothing calls.** Either the FFI
   generator consumes it (in which case the `pass_todo` bodies are correct and
   RET005 should learn to skip `ffi_gen/specs/`), or it is dead weight.
