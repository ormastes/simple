# MCP stdio smoke: seed whole-program flat registry corrupts extract_id() when main_lazy_protocol.spl joins the import closure

**Date:** 2026-07-17
**Scope:** `src/app/mcp/main.spl` (`.spl` fix, DONE) + `src/compiler_rust` interpreter
(NOT fixed here — out of scope per task rules; seed-side).
**Severity:** high — blocks the MCP stdio smoke round-trip on the seed binaries
(`src/compiler_rust/target/release/simple` and `.../target/bootstrap/simple`).

## Symptom 1 (FIXED, pure Simple): `--stdio` flag rejected

`src/compiler_rust/target/release/simple run src/app/mcp/main.spl --stdio`
exited 1 with `[error] mcp: Unknown mcp option: --stdio`. `main()`'s arg
parser (`src/app/mcp/main.spl`, around line 402) only recognized `--help`,
`-h`, `help`, `--version`, `-v`, `--probe` — any other single arg (including
the common MCP-client convention flag `--stdio`) fell through to the
"Unknown mcp option" branch and returned 1. The documented, canonical
invocation (`.mcp.json`, `bin/simple_mcp_server`) always launches with zero
args — stdio framing is the server's only transport, so `--stdio` is
semantically a no-op.

**Fix:** changed the guard from `if args.len() > 0:` to
`if args.len() > 0 and args[0] != "--stdio":`, so `--stdio` now falls through
to the shared serve loop instead of erroring. Minimal, no duplicated logic.

## Symptom 2 (NOT FIXED — seed interpreter defect, out of scope): `extract_id()` corrupts to an `i64` when `main_lazy_protocol.spl` is in the closure

After the `--stdio` fix, the smoke test still exits 1, now with:

```
error: semantic: method `len` not found on type `i64` (receiver value: 4059709571969)
```

(the huge "receiver value" is a pointer-shaped number, not user data — this
is a type-tag/boxing corruption pattern, not a real integer).

Bisected with debug `_mcp_error` markers: the crash happens **inside**
`_mcp_extract_id(msg, "initialize")` — specifically inside
`extract_id`/`extract_field_raw`/`_find_json_value_start` in
`main_lazy_json.spl`, on the very first `initialize` request, before any
response is ever produced. Confirmed identical on:
- `src/compiler_rust/target/release/simple` (interpret mode, default)
- `src/compiler_rust/target/release/simple` with `SIMPLE_EXECUTION_MODE=compile`
- `src/compiler_rust/target/bootstrap/simple`

### Minimal, deterministic repro

`extract_id()` (copied verbatim from `main_lazy_json.spl`, no changes) run
standalone on the exact same message succeeds (`id=1`, exit 0) — proving the
function's own logic is correct. Adding **one unrelated, unmodified sibling
import** to the same file flips the identical call into the crash above:

```simple
use std.io_runtime.{env_get, file_exists, exit, get_args}
use std.nogc_sync_mut.io.stderr_ops.{stderr_write, stderr_flush}
use .mcp_log_options
use std.mcp_sdk.server.method_detect.{has_method}
use .main_lazy_json
use .main_lazy_protocol   # <-- adding ONLY this line flips a working call into the crash

fn main() -> i64:
    val msg = "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{}}"
    val id = extract_id(msg)   # clean (id=1) without the line above; crashes with it
    print "id={id}"
    0
```

`main_lazy_protocol.spl` is never called (`main()` above never invokes any of
its functions) — its mere presence in the whole-program import closure is
enough to corrupt an unrelated call elsewhere. Bisecting inside
`main_lazy_protocol.spl` (halves/quarters) narrowed the trigger to
`handle_resources_read`/`get_cwd`/`make_resource_content_response` together,
but no single-function isolation reliably reproduced it outside the full
file — consistent with whole-program registry-slot corruption rather than a
localized source bug (further narrowing not pursued, per task scope: seed
interpreter internals are out of scope for this lane).

### Why this looks like the same defect class as today's Wall-2/SDNVALUE fixes

`doc/08_tracking/bug/hir_stmt_expr_payload_extraction_nil_2026-07-17.md`
(same date, different lane) already root-caused and fixed **two** instances
of a shared mechanism this session: the interpreter's `classes`/`enums`
lookups are **global/flat across the whole loaded program**, not properly
scoped per module, so a same-named class/enum/function anywhere in the
transitive closure can silently shadow or hijack resolution for a call site
that never intended to reference it (`use_bare_module_fallback` missing
`receiver_is_enum`; `handle_constructor_methods` missing an enum-variant
fallback). This repo's MCP/LSP tree has **dozens** of sibling modules
independently defining identically-named private JSON helpers (`Q`, `LB`,
`RB`, `SB_L`, `SB_R`, `jp`, `js`, `jo1`..`jo4`, `escape_json`,
`extract_field`, `extract_field_raw`, `extract_id` — confirmed via
repo-wide grep across `src/app/mcp/`, `src/app/lsp_mcp/`, `src/app/mcpgdb/`,
`src/app/jupyter_kernel/`, `src/lib/*/mcp_sdk/`, `src/lib/*/lsp/`, etc.),
each file's header comment explicitly noting these are meant to be
**module-private, zero-import inlined copies** ("Local definitions (runtime
can't re-export imported symbols)" / "JSON helpers (inlined for zero-import
startup)"). If the seed's function registry is similarly flat/global (a
function-name analog of the already-fixed class/enum-name collision), this
is a strong candidate root cause: adding `main_lazy_protocol.spl` doesn't
introduce a *new* colliding name (its helper names are already duplicated in
`main_lazy_json.spl`), but it can plausibly perturb which same-named
definition "wins" the global slot, or shift internal ID/slot numbering enough
to corrupt an unrelated already-resolved call. Not independently proven at
the Rust level here (would require `src/compiler_rust` instrumentation,
explicitly out of scope for this lane) — flagged as the most likely
mechanism for whoever picks this up next.

**Tested and disproven, 2026-07-17 (same session, standalone-compile-sweep
follow-up):** replacing `main_lazy_protocol.spl`'s implicit/flat-namespace
reliance on `main_lazy_json.spl`'s helpers with **explicit**
`use .main_lazy_json.{make_json_result, make_error, extract_field,
escape_json, top_level_item_count, shell_cmd, _slice_text}` imports (plus a
`std.io_runtime.{file_read}` import and a latent `NL`→`_PROTO_NL` typo fix —
see
`mcp_main_lazy_json_standalone_compile_process_run_tuple_ambiguity_2026-07-17.md`
for the full changeset) does **not** fix this defect: the exact same
`error: semantic: method \`len\` not found on type \`i64\`` crash reproduces
identically on the smoke test after the explicit-import change, ruling out
"bare-identifier global-fallback resolution" (the exact Wall-2 mechanism) as
this particular defect's cause. Whatever perturbs the registry/slot
numbering here is triggered by something else about `main_lazy_protocol.spl`
joining the closure — not resolved by making its cross-file references
explicit. The explicit imports were kept anyway (they independently fix
`main_lazy_protocol.spl`'s standalone-compile gap, a real, separate
improvement) but this specific runtime defect remains open.

### Impact

Blocks the MCP stdio JSON-RPC round-trip (`initialize` → result) via
`src/compiler_rust/target/release/simple run src/app/mcp/main.spl` (with or
without `--stdio`), on both the release and bootstrap seed binaries. The
`.mcp.json`-registered production path (`bin/simple_mcp_server` →
`bin/release/<triple>/simple`, the self-hosted binary) is a **different**
artifact (compiled, not the interpreter-mode seed) and is not proven to share
this exact defect — separately known-stale per the redeploy wall (not this
bug).

### Status

Not fixed. Per task scope (`src/compiler_rust` is out of scope; "do not edit
Rust"), this is reported with a minimal, deterministic repro for whoever next
works the seed's flat-registry defect class (see the referenced doc's Wall-2
and SDNVALUE fixes for the two already-fixed sibling instances of this same
mechanism). The `--stdio` symptom (Symptom 1) is fixed in `main.spl`; the
underlying round-trip still cannot be verified end-to-end against the seed
binaries until Symptom 2 is resolved in `src/compiler_rust`.

## Pure-Simple compiler audit 2026-07-17 (marker: `pure_interp_registry_2026-07-17`)

Separate lane (Worker T), scoped to `src/compiler/**` (the pure-Simple
compiler's own interpreter), to determine whether the SAME failure mode
(an unrelated/never-called module corrupting an unrelated function's call
elsewhere) exists in our own registry design, not just the Rust seed's.

**Registry map** (`src/compiler/10.frontend/core/interpreter/`):
- `eval_tables.spl` — `func_table_*`/`struct_table_*`: chained-hash maps
  (`ft_keys`/`ft_vals`/`ft_buckets`/`ft_nexts`, same shape for structs),
  keyed by **bare name** (not module-qualified). `func_table_register`
  overwrites on collision (last-write-wins), with a diagnostic-only warning
  for `_`-prefixed private helpers whose signature differs
  (`_ftr_warn_collision`) — public/method (`Type__method`-mangled) names
  collide silently, no warning.
- `value.spl` — separate value arena (`val_kinds`/`val_ints`/`val_texts`/…),
  index-based (`value_id: i64`) with a free-list for slot reuse. Kind is
  stored in a **separate parallel array** (`val_kinds[vid]`), never encoded
  into the value word itself.
- `module_loader_core.spl` — `register_module_functions()` registers a
  module's decls (scanned from the freshly-parsed AST) into the tables
  *after* a successful parse; it does not evaluate function bodies, so an
  unresolved identifier inside a body is never touched at registration time.
- `module_loader_lazy.spl` (gated off by default, `SIMPLE_LAZY_PARSE=1`) —
  outline-scans a module's top-level surface and defers real
  parsing/registration until first symbol use
  (`try_force_any_deferred_for`); a never-called deferred module is never
  parsed at all, let alone registered.

**Audit table** (failure modes a–e from the task; each vs. this design):

| # | Failure mode | Present? | Evidence |
|---|---|---|---|
| a | Bare-name keys allow cross-module collision/overwrite | **Yes** | `eval_tables.spl:168-182` (`func_table_register`, last-write-wins); `eval_tables.spl:480-494` (`struct_table_register`, same, no warning at all — matches the pre-existing `feedback_interp_struct_name_collision_global_registry` note). Method names are mangled `Type__method` at parse time (`parser_decls_use.spl:387`) but still bare-keyed, so two modules each defining a struct of the same name with a same-named method collide too. |
| b | Registration before identifiers resolve, corrupting registry/slot state | **No** | `module_loader_core.spl:257-294` (`register_module_functions`) only reads `decl_get_tag/name/ret_type` off the parsed AST — it never evaluates expressions/bodies, so an unresolved identifier inside a function body cannot reach registration. Confirmed the AST arena is append-only (`core_frontend_parse_append`, `module_get_decls()` scans only the freshly-appended module's decls) so stored `decl_id`s stay stable across later parses. |
| c | Slot/index-based registry where a failed/partial registration shifts later slots | **No** | Both `eval_tables.spl` tables and `value.spl`'s value arena are append-based (`ft_keys.push(...)`, `val_kinds.push(...)`); removal tombstones in place (`func_table_remove` clears key/value, unlinks the hash chain, never compacts) and reuse goes through an explicit free-list (`val_free_list`). No index ever shifts because of another entry's removal or a partial registration. Regression spec: Group 3 in `registry_scoping_spec.spl` (below). |
| d | Double-registration of cross-module fns (seed's FUNCTION_OVERLOADS class) | **N/A / narrower** | The interpreter has no overload table at all — one bare name = one slot, always (no seed-style dual-path double-registration to lose a mut-param writeback). The analogous risk here is (a)'s plain collision, not a writeback-loss bug. |
| e | Silent fallback to a global/flat lookup when scoped lookup misses | **Yes (opt-in path only)** | `module_loader_core.spl:125-148` (`try_force_any_deferred_for`) walks ALL deferred modules and force-loads the *first* one whose recorded export list contains the requested bare symbol name — if two lazily-deferred modules both export the same name, whichever was deferred first wins materialization regardless of which one the caller actually meant. Gated behind `SIMPLE_LAZY_PARSE=1` (default OFF via `lazy_parse_enabled()`), so not on the default path. |

**Verdict: does NOT share the seed's specific failure mode, but has a
related, narrower defect (now fixed).** The seed's symptom
(`method 'len' not found on i64`, a pointer-shaped receiver value) is a
type-tag/boxing corruption: the seed apparently encodes type information
into the value word itself, so a slot/tag mixup makes an integer look
pointer-shaped. The pure-Simple interpreter's value representation
(`value.spl`) stores kind in a **separate** parallel array
(`val_kinds[vid]`), never encoded into the same word as the payload —
structurally, a registry-slot mixup here cannot manifest as "int now looks
like a pointer" the way it does in the seed. Registration is also
strictly decl-scan-based (b) over an append-only AST arena, so an
unresolved identifier in a body cannot perturb registration at all, and
there is no index-shift-on-removal (c) or seed-style double-registration
path (d).

**However**, the audit surfaced a genuine, narrower cross-module
corruption bug in the **unload** path, in the same spirit as (a): if
module A registers `helper` and module B (loaded later) also registers
`helper` (bare-name collision — table now holds B's decl_id), later
selectively unloading A via `interp_unload_module`/`irt_unload_module`
blindly called `func_table_remove("helper")` — deleting B's LIVE
registration, not A's stale one. This is a real "unrelated module's
function disappears" corruption, reachable whenever selective module
unload is used (opt-in API, exported from
`compiler/10.frontend/core/interpreter/__init__.spl`; not on the default
`load_module` hot path).

### Fix (root-cause, additive — no wholesale registry redesign)

- `eval_tables.spl`: added `func_table_remove_owned(name, expected_decl_id)`,
  `func_remove_return_type_owned(name, expected_decl_id)`,
  `struct_table_remove_owned(name, expected_decl_id)` — each no-ops
  (leaves the table untouched) when the table's current entry for `name`
  does not match `expected_decl_id`, i.e. when a different module's
  registration is the one currently live. Existing unguarded
  `func_table_remove`/`func_remove_return_type`/`struct_table_remove` are
  untouched (no signature change, no blast radius on any caller not
  migrated).
- `interp_resource_tracker.spl`: added `irt_func_decls`/`irt_struct_decls`
  parallel arrays recording the owning `decl_id` per tracked name; new
  `irt_track_func_owned`/`irt_track_struct_owned` hooks populate them (the
  old `irt_track_func`/`irt_track_struct` still work, pushing a `-1`
  sentinel so array lengths stay lockstepped — `irt_unload_module` falls
  back to the old unguarded removal only for `-1`-sentinel/legacy entries).
  `irt_unload_module` now calls the `_owned` removal variants whenever an
  owner decl_id was recorded.
- `module_loader_core.spl`: the 4 call sites in `register_module_functions`
  (`DECL_FN`, `DECL_EXTERN_FN`, `DECL_STRUCT`, `DECL_IMPL` methods) now call
  `irt_track_func_owned`/`irt_track_struct_owned` with the decl's own id.
- `__init__.spl`: re-exports the new `_owned` functions alongside their
  existing counterparts.

### Regression spec

`test/01_unit/compiler_core/interpreter/registry_scoping_spec.spl` — mocks
mirroring the real guarded logic (same "hm_* not importable standalone in
interpreter-mode runtime" constraint documented in the neighboring
`interp_resource_tracker_spec.spl`, same directory). 7 examples, 0
failures via `timeout 240 src/compiler_rust/target/release/simple test
test/01_unit/compiler_core/interpreter/registry_scoping_spec.spl` (exit 0):
pins the CURRENT bare-name collision policy (last-write-wins — not changed
to fail-closed; that would be a wholesale redesign and contradicts the
codebase's documented diagnostic-only choice for the private-helper case),
proves the pre-fix unguarded unload deletes a surviving module's entry
(regression proof) and that the guarded unload does not, and confirms a
later module's partial registration never shifts/corrupts an earlier
module's already-registered slots.

**Verifiability caveat:** the pure-Simple binary (`bin/release/<triple>/simple`)
is too stale to exercise these source edits end-to-end (redeploy wall,
separate campaign) and a full bootstrap was out of scope for this lane;
the regression spec runs its own faithful mock of the guarded logic on the
seed binary, not the compiled `eval_tables.spl`/`interp_resource_tracker.spl`
themselves. The source edits are reviewed/read-verified but not
build-verified in this pass.
