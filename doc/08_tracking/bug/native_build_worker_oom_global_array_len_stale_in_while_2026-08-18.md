# Native-build worker 2^34 OOM: module-global array `.len()` is STALE in a while condition while `.push()` grows the live vec — a fill loop that never terminates

- **Filed:** 2026-08-18
- **Status:** ROOT-CAUSED and WORKED AROUND (compiler-source fix landed in
  `src/compiler/10.frontend/desugar/placeholder_lambda.spl`); the underlying
  INTERPRETER defect (stale global read in loop conditions) remains OPEN.
- **Predecessor rows:** `native_build_interpreted_worker_rss_blowup_2026-08-18.md`
  (term-2 creep, 2^31 datum), `native_build_source_closure_zero_sources_2026-08-17.md`.
  The task-orders row `prepush_hook_unpassable_native_build_oom_2026-08-17.md`
  does not exist in this worktree (presumed lost to the 2026-08-18 reconcile
  clobber); its measured facts were relayed in the task order and are all
  reproduced/confirmed below.

## The captured call site (deliverable 2 — verbatim)

Guard: `mem_trace.rs` big-alloc reporter (`SIMPLE_BIG_ALLOC_MB=256`), run on the
instrumented seed (`/mnt/data/cargo-alloc-hunt/release/simple`, built 2026-08-18
08:34 from this tree) with the task's repro
(`SIMPLE_NATIVE_BUILD_WORKER=1 ... run src/app/cli/native_build_worker.spl
--entry tiny.spl`, `ulimit -v 27000000`). Log:
`/tmp/claude-1000/-mnt-data-worktrees-simple-main/0dc81a3e-6ed7-4e58-a9de-aa20fd7b649d/scratchpad/oomrepro/run2.log`.

```
[mem][BIG] realloc request of 17179869184 bytes (16384.0 MB = 2^34)  while live=10638.2MB rss=11014.7MB allocs=766769762
[mem][BIG] interp stack (innermost first, depth 9): transform_placeholder_call_args_after_interpolation <- parse_and_build_module_scoped <- parse_full_frontend_with_scope <- parse_full_frontend <- parse_all_impl <- compile <- compiler_driver_run_compile <- cli_native_build <- main
[mem][BIG] backtrace:
   1: __rustc::__rust_realloc
   4: simple_compiler::interpreter::interpreter_helpers::patterns::apply_array_mutation_in_place
   5: simple_compiler::interpreter::interpreter_helpers::patterns::handle_method_call_with_self_update
   6: simple_compiler::interpreter::node_exec::exec_node
   7: simple_compiler::interpreter::block_exec::exec_block
   8: simple_compiler::interpreter::interpreter_control::exec_while
   ...
memory allocation of 17179869184 bytes failed        (rc=134)
```

The full ladder was captured in ONE run: 2^28, 2^29, ... 2^33, 2^34, every one
the SAME `vec.push` inside the SAME while loop, live≈10.6 GB at the 2^34 abort —
byte-for-byte the incident signature (16 GiB single request at ~10.9 GB held).

## Root cause

`transform_placeholder_call_args_after_interpolation`
(`src/compiler/10.frontend/desugar/placeholder_lambda.spl:342`) filled a
MODULE-GLOBAL marks array:

```
_ph_pattern_node_marks = []
while _ph_pattern_node_marks.len() < initial_expr_count:
    _ph_pattern_node_marks.push(false)
```

Under the Rust-seed interpreter, `.push()` on the module-global grows the live
vec (via `apply_array_mutation_in_place` + self-update writeback into the local
env), but `.len()` in the while CONDITION keeps reading a stale copy pinned at
its initial value. The condition never becomes false; the vec doubles
256 MB → 512 MB → ... → 16 GiB until the allocator aborts. `initial_expr_count`
was **4** (tiny.spl) — the bound was never the problem.

The "ladder exactly 3 bits apart" (2^31 / 2^33 / 2^34 across incidents) is NOT
a tagged-count shift: it is Vec growth-by-doubling caught at different memory
limits. One hypothesis measured, replaced by a better-supported one.

**Minimal repro (11 lines, no compiler involved):**
`.../scratchpad/oomrepro/globalfill.spl`

```
var g: [bool] = []

fn fill(n: i64):
    while g.len() < n:
        g.push(false)

fn main() -> i64:
    fill(3)
    print g.len()
    0
```

`SIMPLE_EXECUTION_MODE=interpret <seed> run globalfill.spl` under
`ulimit -v 2000000` → `memory allocation of 536870912 bytes failed`, rc=134.
Reproduced 2026-08-18 on the instrumented seed. **This is the open interpreter
defect:** any `while <module-global>.len() < n: <module-global>.push(...)` loop
is an OOM bomb. (Sibling of the writeback family:
`aliased_array_mut_param_mutation_lost_interpreter_2026-08-06.md`,
`chained_static_ctor_receiver_drops_mutation_2026-08-01.md`.)

## Fix landed (compiler source — no rebuild needed, stdlib/compiler read as source)

`placeholder_lambda.spl` now fills on a LOCAL counter (`var mark_fill = 0;
while mark_fill < initial_expr_count: push; mark_fill += 1`), with a comment
pointing here. Before/after, same repro, same host, `ulimit -v 8 GB`:

Two-step fix, because the stale-global defect bites twice: (1) loop on a local
counter instead of `.len()` of the global (kills the OOM; run5 then failed
`array index out of bounds: index is 0 but length is 0` because push-built
contents ALSO never reach later global reads); (2) build the marks in a LOCAL
vec and assign the global ONCE — whole-array assignment and `g[i] = x` index
stores DO propagate (verified by `globalassign.spl`, printed `3` / `marked ok`).

| arm | outcome (same repro, same instrumented seed, `ulimit -v` 27/8 GB) |
|---|---|
| before | rc=134 abort, single 2^34-byte (16 GiB) realloc at ~10.6 GB live; ladder 2^28..2^34 all from one `vec.push` loop |
| after | **rc=0, full 6-step pipeline, WALL=54.9 s, MAXRSS=2.97 GB**; `tiny.bin` produced (23 KB) and prints `hi` (exit 0) |

The remaining 2.9 GB is the previously-filed fixed term-1 import-closure floor
(`native_build_interpreted_worker_fixed_2_4gb_floor_2026-08-18.md`), untouched
here. This row closes the pre-push-blocking abort: the worker had NEVER before
gotten past `parse 0/1` on even a 3-line entry.

A sweep of `while X.len() <` across `src/compiler` + `src/app/cli` found the
other ~20 sites all loop on LOCALS, which do not trigger the stale-read defect.

## Instrumentation landed (reusable)

- `src/compiler_rust/compiler/src/mem_trace.rs`: big-alloc guard was already
  added by a parallel lane (checks size BEFORE the inner allocator so the
  FAILING request is reported; `SIMPLE_BIG_ALLOC_MB=<n>` or `SIMPLE_MEM_TRACE=1`,
  256 MB floor). THIS lane added on top: a TLS **interpreted-function name
  stack** (`InterpFrame`, maintained only when the guard is on) dumped in every
  big-alloc report — it is what named the .spl function.
- `src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs`:
  one `InterpFrame::enter(&func.name)` at the `execute_function_body` choke
  point (one cached-bool branch when the guard is off).

## Regression test

The 11-line `globalfill.spl` above is the red repro for the interpreter defect.
It is deliberately NOT added to the test tree yet: it is red under the current
seed (rc=134 abort), and adding a known-red test violates the no-skip rule.
When the interpreter stale-global-read defect is fixed, add it as a spec
asserting `g.len()` prints 3. The placeholder-lambda fix itself is exercised by
every native-build worker run (the worker previously could not get past parse
of even a 3-line entry).

## Not done / open

- Interpreter fix for the stale global read in while conditions — OPEN, above.
- `run3.log` incidentally shows `.str()` is not a method on `i64` under the
  seed interpreter (`method 'str' not found on type 'i64'`) — pre-existing gap,
  noted only.
