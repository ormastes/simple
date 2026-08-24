# Importing `std.io_runtime` breaks `native-build` — `method 'len' not found on type 'i64'` (2026-08-24)

- **Status:** FIXED 2026-08-24 (see final section) — the localization in the earlier sections is superseded
- **Severity:** HIGH — blocks building the MCP server locally, and any app that
  touches `std.io_runtime`
- **Area:** seed interpreter extern dispatch + the
  `std.io_runtime` <-> `io/process_ops` <-> `io/process_governor` import cycle
- **Found by:** attempting a local MCP build through the interpreted pure-Simple
  compiler

## Four-line reproducer

```
use std.io_runtime.{env_get}

fn main() -> i64:
    print("ok")
    return 0
```

```
cd src/compiler_rust && cargo build --release --bin simple     # 2m08s, current seed
target/release/simple run src/app/cli/bootstrap_main.spl native-build repro.spl -o /tmp/out
-> error: semantic: method `len` not found on type `i64` (receiver value: 38)
-> rc=1, no binary produced
```

`env_get` is never called. **The import alone is sufficient.**

## Isolation (each row measured, cold cache, same worktree and seed)

| fixture | result |
|---|---|
| no imports at all, `print("ok")` | **builds, rc=0** |
| `use std.nogc_sync_mut.io.stderr_ops.{stderr_write}` | **builds, rc=0** |
| `use std.io_runtime.{env_get}` | FAILS, receiver value 38 |
| `use std.io_runtime.{env_get, file_exists, exit, get_args}` | FAILS, receiver value 38 |
| `use std.nogc_sync_mut.io.process_ops.{process_run_bounded}` | FAILS, receiver value **254** |
| `use std.nogc_sync_mut.io.process_governor.{proc_slot_acquire}` | FAILS, receiver value 38 |
| `src/app/mcp/main.spl` (the real target) | FAILS, receiver value 38, at parse 11/61 |

**The receiver value is not stable** (38 vs 254 for different entry imports), so
it is a corrupted handle, not user data — the same reading the
`seed_flat_registry_len_i64_2026-07-17` comments in
`interpreter_extern/sffi_string.rs:281` and `interpreter_extern/mod.rs:3255`
give for this message shape.

## What it is NOT

- **Not caused by the dict keys/values HIR typing** (`fb7e76c489a` /
  `c9da626ec1c`). Control: reverting `expression_core.spl` to the pre-fix
  content in the same worktree, cold cache, reproduces the failure IDENTICALLY.
- **Not a plain extern-registry gap of the obvious kind.**
  `scripts/check/check-interpreter-extern-registry-gap.shs` reports
  `PASS — 282 symbol(s) checked, 0 new, 0 stale`, and all four array-returning
  externs declared in `io_runtime.spl` (`rt_file_read_bytes`, `sys_get_args`,
  `rt_dir_list`, `rt_dir_walk`) DO have `insert_simple!` handlers in
  `interpreter_extern/mod.rs` (lines 1366, 2436, 1203, 1206).
- **Not the same manifestation as
  `mcp_stdio_smoke_seed_flat_registry_len_i64_2026-07-17.md`** (OPEN, P2), though
  it is the same family and that record should be read alongside this one. That
  one fires at RUNTIME of an already-built MCP server, inside
  `_mcp_extract_id()`, with a pointer-shaped receiver (4059709571969), and was
  last re-verified by SOURCE INSPECTION. This one fires at BUILD time, from a
  four-line file with no MCP in it, with small receiver values, and is verified
  by EXECUTION. It blocks strictly earlier: there is no binary to run.

## Lead worth pulling first: a module cycle

`std.io_runtime` imports `std.nogc_sync_mut.io.process_ops`
(`io_runtime.spl:13`), and `process_ops` imports `std.io_runtime` right back
(`process_ops.spl:13,41,42,43,44`), as does `process_governor`
(`process_governor.spl:11,12`). Every fixture that fails pulls this cycle in;
the two that build (`stderr_ops`, no-imports) do not. Whether the cycle is the
cause or merely correlates with the real culprit is NOT established here.

Second lead: `process_ops.spl:10,12` declare TUPLE-returning externs
(`rt_process_run(...) -> (text, text, i64)`), a shape with its own history of
payload-extraction defects.

## Impact

`bin/simple_mcp_server` cannot be built locally through the interpreted lane
today. A fresh seed CAN otherwise run the pure-Simple compiler end to end —
hello world and dict fixtures compile, link, and run — so this single defect,
not the Stage 2 blocker, is what stands between this host and a locally built
MCP server.

## NOT verified

- The exact extern or compiler site that produces the bad receiver was not
  identified. The `.len()` is called inside pure-Simple compiler code while the
  seed interprets it; no source location is printed with the diagnostic.
- The cycle hypothesis is a lead, not a diagnosis — no experiment was run that
  breaks the cycle and shows the failure disappearing.
- Nothing was fixed. This record exists so the next lane starts from a four-line
  reproducer instead of a 61-module MCP build.

## 2026-08-24 (later) — both leads REFUTED by experiment, and the search space is now one file

Both hypotheses recorded above were tested and **both are wrong**. Recorded so
nobody re-runs them.

### Lead 1 (import cycle): REFUTED

The cycle edge is `io_runtime.spl:13`, `use std.nogc_sync_mut.io.process_ops
.{process_run_bounded}`, which exists ONLY so line 488 can re-export the name.
Deleting that line and dropping `process_run_bounded` from the export list makes
**`io_runtime` a leaf with no `use` lines at all** — the cycle is definitively
gone, not merely reduced.

The four-line fixture still fails, byte-identically:

```
error: semantic: method `len` not found on type `i64` (receiver value: 38)
```

So the cycle is not the cause. It correlated only because every failing fixture
happened to pull that region of the tree.

**This is the useful part of the refutation:** with `io_runtime` a leaf that
still reproduces, the culprit is inside `io_runtime.spl`'s own 488 lines. The
search space went from "the std import graph" to one file.

### Lead 2 (tuple-returning externs): REFUTED, in both forms

`process_ops`/`io_runtime` declare `rt_process_run(...) -> (text, text, i64)`,
and a tuple ABI mismatch would explain a receiver that is not the value you
expect. Two separate fixtures, both **build cleanly (rc=0)**:

| probe | shape | result |
|---|---|---|
| T1 | imported module DECLARES a tuple-returning extern; fixture imports a non-tuple fn from it | builds |
| T2 | fixture imports the tuple-returning function itself, across a module boundary | builds |

T2 matters because it is the shape `io/env_ops.spl:7` actually uses
(`use std.io_runtime.{process_run, env_set as io_env_set}` — `process_run`
returns `(text, text, i64)`). That exact shape is fine in isolation.

### A bisection note for whoever continues

Truncating `io_runtime.spl` to a prefix does NOT work: the rest of the tree
depends on its full export surface, and the build fails early with
`error[E1002]: function 'io_env_set' not found` (from
`src/lib/nogc_sync_mut/io/env_ops.spl:7,46`) before it ever reaches the
corrupting code. Any bisect must PRESERVE the exported surface — stub bodies
rather than delete declarations.

Also note `src/std/nogc_sync_mut/io_runtime.spl` and
`src/lib/nogc_sync_mut/io_runtime.spl` are the SAME file (a `cp` between them
reports "identical (not copied)"), so editing one edits both; do not waste a
run thinking you are testing two variants.

### Status

Three hypotheses eliminated (cycle; tuple extern declared; tuple fn imported),
one file localized, nothing fixed. No further hypothesis was pursued rather than
casting around for one.

## 2026-08-24 (later still) — ROOT CAUSED and FIXED. It was never about `io_runtime.spl`.

**Status of this defect: FIXED** by `parse_match_arms_common` / `parse_receive_stmt`
local renames in `src/compiler/10.frontend/core/parser_stmts.spl`.

### The localization above was wrong, and the reproducer is much smaller

`io_runtime.spl` is not special. The real trigger is **any non-entry module that
contains a `match` statement**. `io_runtime.spl` merely happens to contain three
(lines 144, 172, 177). Seven-line reproducer, no `std` import anywhere:

```
# matchmod.spl
pub fn pick(n: i64) -> i64:
    match n:
        case 0: 10
        case _: 20
```
```
# mmain.spl
use matchmod.{pick}
fn main() -> i64:
    print("v={pick(0)}")
    return 0
```
-> `error: semantic: method 'len' not found on type 'i64' (receiver value: 1)`

The entry file's own `match` statements do not trigger it; only an imported
module's do. That is why hello-world and `stderr_ops` (0 `match`) built and every
`io_runtime` fixture did not.

### How it was found (technique worth reusing)

The seed already carries a level-gated probe at the error site
(`SIMPLE_INTERP_OOB_DEBUG`, `compiler/src/interpreter_method/mod.rs`), but it
printed only a *Rust* backtrace, which names interpreter dispatch frames and not
the interpreted `.spl` function. Adding `debug_call_stack_snapshot()` to that
probe (populated when `SIMPLE_DEBUG_FIELD_ACCESS=1`) printed the interpreted
stack in one run:

```
main -> run_native_build_bootstrap -> compiler_driver_run_compile -> compile
 -> parse_all_committing_impl -> ... -> parse_and_build_module_scoped
 -> flat_pools_dump_all -> flat_decl_pools_dump
 -> flat_pool_enc_i64_list -> flat_pool_enc_i64
```

So the failure is on the **frontend cache STORE path**, after a successful parse,
not in the parser proper. `flat_pool_enc_i64_list(pool: [[i64]])` iterated a pool
whose element was a bare `i64`. A temporary `print` before each
`flat_pool_enc_i64_list` call in `flat_decl_pools_dump` named the pool:
**`arm_body`** (`_Ast/decl_nodes.spl:1240`, `var arm_body: [[i64]] = []`).

### Root cause (proven by experiment)

Probes placed inside `arm_new_with_binding_and_rationale` show the arena is
CORRECT when built:

```
[armnew] body=[0]      [armnew-after] arm_body=[[0]]
[armnew] body=[1]      [armnew-after] arm_body=[[0], [1]]
```

and CORRUPT by the time the dump reads it:

```
[dump] arm_body=[1]        <- flat [i64], not [[i64]]
```

`parser_stmts.spl` declared **function-local** variables named `arm_body`
(`:1790` `val`, `:1827` `var`, `:1956` `val`), each of type `[i64]` — the same
name as the `[[i64]]` module-global arena owned by `_Ast/decl_nodes.spl`. Under
the seed interpreter the parser's local write reached the global, replacing the
`[[i64]]` arena with the last arm's flat `[i64]` body. The encoder then called
`.len()` on `1`, an element of that flat list. The unstable "receiver value"
(38 / 254 / 1) is simply the last arm body's element, which of course differs
per input — consistent with "corrupted handle" only by coincidence.

**Fix:** rename those three locals to `case_arm_body`. Nine token replacements,
no behaviour change, no rename of the arena or of `arm_body_flat`.

Verified: the seven-line `matchmod` fixture now builds (rc=0), links, and the
binary RUNS printing `v=10`.

### Corrections to earlier entries in this record

- "the culprit is inside `io_runtime.spl`'s own 488 lines" — **wrong**. The
  refutation of the cycle hypothesis was sound; the inference drawn from it was
  not. `io_runtime` is a trigger input, not the defective code.
- The comment at `_Ast/decl_nodes.spl:1241-1247` explains `arm_body_flat` as a
  workaround for the seed "erasing the inner list of a `[[i64]]` to a boxed i64
  handle". That theory is **superseded**: there is no erasure. A control fixture
  (module-global `var pool: [[i64]]`, cross-module push/read/iterate) round-trips
  correctly under the same seed. `arm_body_flat` is left in place — it is
  harmless and independently load-bearing for reads today — but it was treating
  a symptom of the name collision.

### What is NOT fixed, and is filed separately

The underlying **interpreter defect** — a function-local binding in one module
writing through to a same-named module-global in another module — is not fixed
here. See
`doc/08_tracking/bug/interp_local_shadows_cross_module_global_arm_body_2026-08-24.md`.

The mechanism is **not fully characterized**, and a naive statement of it is
contradicted by evidence in this same tree: a scan for the same shape found
latent same-class sites that demonstrably do **not** fire —
`val decl_span = flat_span_new(...)` at `parser_decls_use.spl:475,488,506,524`,
`_ParserDecls/fn_struct_decls.spl:666,724`,
`_ParserDecls/enum_module_body.spl:571,918` (local `i64` vs global `[i64]`),
`interpreter/eval_decls.spl:29` (`decl_name`), and
`compiler/cg_stmt.spl:518` (`arm_body` again). After the fix the same build
passes parse and cache-dump cleanly, so those shadows are not clobbering. What
distinguishes the firing case from the non-firing ones is an open question. They
are deliberately NOT renamed: renaming code that provably does not misbehave
would be speculative churn.

### A LATER, DISTINCT defect is now exposed

With this fixed, the original four-line `std.io_runtime` fixture gets past parse,
HIR and into MIR, and fails on something else entirely — a borrow-checker
verdict, six times, in the `std.io_runtime` closure:

```
[ERROR] Borrow error: 43:1: borrow of `local(13)` may still be active at return
        |||RELATED:6:1:borrow created here|||HELP:ensure borrow ends before returning
(also 37:1, 54:1, 66:1, 73:1, 79:1)
```

That is a separate bug and is tracked on its own; it was previously unreachable
behind this one.

## 2026-08-24 (end of lane) — the full chain, and where it actually stops

This record opened as "the one defect standing between this host and a locally
built MCP server". That framing was wrong: it was the FIRST of five. Recorded
here as an index so nobody re-derives the ordering.

| # | defect | status |
|---|---|---|
| 1 | `arm_body` local/global collision -> `method 'len' not found on type 'i64'` | **FIXED** `ec272de6947` |
| 2 | `val x = unsafe(...):` parsed by the seed as a call to `unsafe` | **worked around at all 3 call sites** `495af8df740`, `7ec9ae025ee` (seed defect itself OPEN) |
| 3 | NLL reports `&mut` of a local "may still be active at return" at every return | **OPEN**, 10-line reproducer filed |
| 4 | no MIR/HIR lowering for `(a, b) = expr` | **FIXED** `b102d597ec1` |
| 5 | `for-in over non-array iterables ... (#143)` | **OPEN** — a known numbered feature gap, not a bug |

**Where each target stands:**

- The four-line `std.io_runtime` fixture in this record **still does not build.**
  It clears defects 1, 2 and 4 and stops on defect 3.
- `native-build src/app/mcp/main.spl` went from dying at **parse 11/61** to
  clearing parse, HIR and MIR lowering for **all 61 modules**, and stops on
  defect 5. No binary is produced.

**Correction to `7ec9ae025ee`'s commit message.** It says the MCP build showed
"zero borrow errors in that closure". That is not evidence of anything:
`borrow_check()` runs AFTER `lower_to_mir` completes
(`80.driver/driver_aot_pipeline.spl`), and every MCP run so far has died INSIDE
`lower_to_mir`. **The borrow checker has never executed on the MCP closure.**
MCP imports `std.io_runtime`, which pulls
`io/process_ops.spl:229 process_read_stdout_result` — the exact function that
produces defect 3. So the predicted chain for the next lane is:

```
clear #143  ->  defect 3 (NLL false positive) fires on the MCP build  ->  unknown beyond
```

Treat defect 3 as queued behind #143, not as absent.

**#143 is broad, measured.** A probe on the error site
(`50.mir/mir_lowering_stmts.spl:2761`) counted **32** offending `for-in`
statements across the MCP closure — it is not one or two call sites that could
be rewritten. The probe also showed every one of those spans is EMPTY
(`file= line=0`): for-body spans are not populated at MIR lowering, so #143
cannot be localized from its diagnostic without instrumenting the compiler.
That is worth fixing alongside #143.

**One negative result in this record is weaker than it reads.** The claim above
that "there is no erasure — a control fixture with a module-global
`var pool: [[i64]]` round-trips correctly under the same seed" is a NEGATIVE
from a small fixture. A sibling lane established today that a minimal fixture
and the real compiler can lower the SAME source by different paths, so a fixture
that does not reproduce may simply not be exercising the same code. The
positive evidence is unaffected and is what the diagnosis rests on: the arena
was observed correct after the pushes and corrupt at the dump, and renaming the
parser's locals eliminated the failure entirely.

**Not related to the Stage-2 `is_empty()` predicate misread** reported by a
sibling lane the same day, despite both being method-call misbehaviour:

- the receiver values here (38 / 254 / 1) are **not** corrupted handles. They
  are ordinary user data — the last match arm's body statement index — which is
  why they varied per input;
- the receiver is neither erased nor a field: it is an element read directly out
  of a module-global array;
- this lane runs the SEED INTERPRETING the pure-Simple compiler, not
  Stage-2-compiled code, so the Stage-2 lowering path is not involved;
- the fix is a rename, with no dispatch change of any kind.

For the record, none of the code landed by this lane uses `.is_empty()`; every
guard added is `.len()`-based.
