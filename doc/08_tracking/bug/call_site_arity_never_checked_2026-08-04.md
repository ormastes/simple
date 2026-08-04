# Call-site argument count is never checked before codegen (2026-08-04)

**Status:** OPEN (detection not armed). Seven real in-tree call sites found; the
two unambiguous ones were fixed in `af0fdf192d8`, and the remaining five
(`awk_tool.spl`) are **now fixed too** — see §7. All seven known call sites are
therefore repaired; what remains open is only the *detection*, per §5.
**Class:** silent corruption — wrong value, exit 0, no diagnostic.
**Related:** `trait_conformance_check_ignores_arity_2026-08-04.md` (`f4a4703f0fb`,
`34e7d0f303b`) closed the *trait/impl name* half. This doc is the *call site*
half, which that work does not cover. Also `test/cert/tool_qual/known_defects/`
failure mode **TOR-FM-02**.

## 1. Probe table (deployed `bin/release/x86_64-unknown-linux-gnu/simple`)

Probes: `f3(a,b,c) -> c*1000 + a*10 + b`, called `f3(7,8)` (one too few) and
`f3(7,8,9,11)` (one too many). A correct 3-argument call yields **9078**; a
missing parameter read as the nil sentinel **3** yields **3078**, which is the
signature to look for.

| call form | too FEW args | too MANY args |
|---|---|---|
| **JIT** (`bin/simple run`, the default engine) | | |
| free `fn` | **9078 → 3078**, exit 0, silent | 9078, extra arg silently DROPPED, exit 0 |
| `me` method | **9078 → 3078**, exit 0, silent | **CRASH** `runtime error: field access on nil receiver`, core dump, **exit 132** |
| `static fn` | **9078 → 3078**, exit 0, silent | 9078, extra arg silently DROPPED, exit 0 |
| **interpreter** (`SIMPLE_EXECUTION_MODE=interpret bin/simple run`) | | |
| free `fn` | `error: semantic: function expects argument for parameter 'c', but none was provided`, exit 1 | `error: semantic: function expects 3 argument(s), but more were provided`, exit 1 |
| `me` method | same error, exit 1 | same error, exit 1 |
| `static fn` | `error: semantic: unknown static method s3 on class Util`, exit 1 (a *different*, unrelated interpreter gap — statics are not registered, so the arity path is never reached) | same |
| **tree-walk under `bin/simple test`** | | |
| free `fn` | example FAILS with the interpreter message | example FAILS with the interpreter message |
| `me` method | example FAILS with the interpreter message | (not probed separately; same path) |

The interpreter's rejection is **evaluation-time**, not a pre-pass: an
unexecuted cold path never fires it. Under the default JIT engine nothing fires
at all.

Reproduce: `test/cert/tool_qual/known_defects/arity_{too_few,too_many,method_too_few,method_too_many,static_too_few}.spl`.

## 2. Where arity *should* be checked, and why it is not

Three independent gaps, in the order a call travels:

### 2a. Pure-Simple semantics — the check exists but is deliberately disabled
`src/compiler/35.semantics/resolve.spl`, `Resolver.fill_call_defaults()`. The
in-tree comment states it outright:

> Arity-error half intentionally omitted (M12 3b). The lean bridge currently
> hardcodes `has_default: false` (`_FlatAstBridge/convert_nodes.spl:571/682`),
> so emitting a "too few arguments" error here would FALSE-FIRE on every valid
> omitted-default call. … Re-enable the arity error only after the bridge
> captures `has_default` faithfully.

The blocking hardcode is real and still present:
`src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl:1581,1692,1813` all
write `has_default: false`. Scope note: even once re-enabled this pass only sees
**direct free-function `Var(sym)` calls whose signature is in the current
module's `module_functions`** — methods, statics and cross-module callees were
never in scope.

### 2b. The Rust seed has no front-end arity check at all
`src/compiler_rust/compiler/src/semantics/` contains only `binary_ops.rs`,
`cast_rules.rs`, `truthiness.rs`, `type_coercion.rs` — no call-arity rule.
`hir/lower/expr/calls.rs` checks arity only for the builtin special forms
(`future`, `await`, `panic`, `range`). This matters because the deployed
`bin/simple` **is** the Rust seed today, so a pure-Simple-only fix would change
nothing observable.

### 2c. The Cranelift lowering silently *adapts* the mismatch
`src/compiler_rust/compiler/src/codegen/instr/calls.rs`,
`adapt_args_to_signature_with_signedness()` pads missing arguments with tagged
nil and truncates extra ones — that is exactly the observed 3078 / dropped-arg
behavior. It already detects the condition and warns, but the warning is gated
behind an env var and is off by default:

```
if arg_vals.len() < expected_count && std::env::var("SIMPLE_STRICT_VREG").is_ok() {
    eprintln!("[codegen-warn] call arity mismatch: got {} args, callee signature expects {} — padding missing args with tagged nil", ...);
```

Positive capability probe confirming the mechanism:

```
$ SIMPLE_STRICT_VREG=1 bin/simple run free_few.spl
[codegen-warn] call arity mismatch: got 2 args, callee signature expects 3 — padding missing args with tagged nil
free_few c_slot=3078
```

The warning has no callee name (only a `FuncRef`), and this adapter is on the
runtime/SFFI path too, so un-gating it as-is is not a usable diagnostic.

### 2d. Only place arity IS enforced
`src/compiler_rust/compiler/src/interpreter_call/core/arg_binding.rs`
(lines 174/188/271/347/386/465) — at argument-binding time inside the
interpreter. Runtime, not compile time.

## 3. Blast radius (measured before arming anything)

Census method (scratchpad script, not committed; algorithm below is the whole
of it). Deliberately conservative, matching what a same-file check could safely flag:
same file only, module-level `fn` definitions only, name defined exactly once in
the file, name not also imported, no defaults / varargs / trailing commas in the
signature, positional call sites only, skipping trailing-block and
trailing-`\`-lambda call forms and AOP pointcut patterns.

**35,330 `.spl` files scanned → 14 mismatching call sites in 9 files.**

| file | line(s) | callee | want | got | verdict |
|---|---|---|---|---|---|
| `src/app/gc/core.spl` | 299 | `gc_mark_object` | 2 | 1 | **REAL — fixed here** |
| `src/os/tools/shell/awk/awk_tool.spl` | 49, 71, 99, 127, 139 | `_exec_action` | 8 | 7 | **REAL — NOT fixed, see §4** |
| `src/app/ui.render/core.spl` | 44 | `render_llm_dashboard` | 1 | 2 | **REAL — fixed here** |
| `test/cert/tool_qual/known_defects/arity_too_few.spl` | 8 | `add` | 2 | 1 | intentional fixture |
| `test/cert/tool_qual/known_defects/arity_too_many.spl` | 8 | `add` | 2 | 3 | intentional fixture |
| `test/{01_unit,unit}/compiler_core/parser/pipe_operator_spec.spl` | 12 | `add` | 2 | 1 | census FP — `1 \|> add(2)` pipe desugaring |
| `src/compiler_rust/lib/std/src/spec/gherkin.spl` | 355 | `step_def` | 3 | 4 | census FP — trailing `\params:` lambda |
| `src/compiler_rust/lib/std/src/concurrency/channels.spl` | 164, 299 | `channel` | 0 | 1 | needs triage (likely doc-example context) |

So: **7 genuine defects in 3 source files**, 2 intentional fixtures, 5 artifacts
of the textual census that an AST-based check would not produce.

**Scope caveat — this number is a floor, not the answer.** The census covers
*only* module-level free functions called by bare name in the same file. It says
nothing about (a) cross-module calls, (b) `me`/`static` method calls, (c) calls
through defaulted parameters, (d) named-argument calls. Those populations are
much larger and their blast radius is **unmeasured**. That is precisely why
nothing is armed as an error in this change.

## 4. Not fixed in `af0fdf192d8` — `awk_tool.spl` signature drift (RESOLVED, see §7)

`_exec_action/8` is called with 7 arguments at five sites, so `vars: [(text,text)]`
is the nil sentinel. It is worse than a pure arity slip: the function returns
`(i32, [(text,text)])` and every caller binds it as a bare `i32`
(`val ctrl = _exec_action(...); if ctrl == 1`). Repairing it means threading awk
variable state through the main loop and destructuring the tuple return — a
feature-level repair, not a call-site edit, and out of scope for this lane.
Recorded here rather than silently normalized.

## 5. What must happen before this can become an ERROR

Ordered, each independently landable:

1. **Unblock the pure-Simple check.** Make
   `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl` capture
   `has_default` faithfully at lines 1581 / 1692 / 1813, then re-enable the
   arity-error half of `fill_call_defaults()` in `35.semantics/resolve.spl`.
   Until the bridge is fixed, arming it false-fires on every valid
   omitted-default call.
2. **Add the seed-side front-end check**, since the seed is what runs today:
   a rule in `hir/lower/expr/calls.rs` (callee name and signature are both in
   scope there) rather than in `adapt_args_to_signature`, which is a lowering
   adapter shared with the runtime/SFFI boundary and cannot name the callee.
3. **Extend the census to methods, statics and cross-module callees** and
   re-measure. Only after that population is known and cleaned can the
   diagnostic be promoted from warning to error.
4. Then promote, and move the five `arity_*` fixtures out of `known_defects/`
   into `../negative/` so the gate enforces rejection.

Arming step 2 before step 3 would turn every latent violation into a hard error
and break `main` — the failure mode a parallel lane hit earlier today at a cost
of ~60 commits of breakage.

## 6. Changed in this commit

- `src/app/gc/core.spl:299` — `gc_mark_object(child_ptr)` →
  `gc_mark_object(gc, child_ptr)`. The recursive child-marking call passed the
  child pointer as the `gc: GCCore` receiver and left `ptr: i64` as sentinel 3,
  so `header_ptr = 3 - 32 = -29` and the mark phase performed a wild
  `read_u8(-29)`. GC child traversal was broken outright.
- `src/app/ui.render/core.spl:44` — `render_llm_dashboard(config, store)` →
  `render_llm_dashboard(config)`; dropped the orphaned
  `var store = AgentDashboardStore()` (`AgentDashboardStore` is not even
  imported — leftover from the simple-ide migration).
- `test/cert/tool_qual/known_defects/arity_method_too_few.spl`,
  `arity_method_too_many.spl`, `arity_static_too_few.spl` — new repros covering
  the method and static call forms, including the exit-132 receiver-displacement
  crash that the free-function form does not exhibit.
- `test/cert/tool_qual/known_defects/README.md` — added the three rows and
  **corrected the existing `arity_too_few.spl` row**, which claimed the program
  prints `1`. It prints `4`: `add(1)` leaves `b` as the nil sentinel 3, so the
  result is `1 + 3`. The corrected value is the sentinel signature itself.

Gate after the change:
`test/01_unit/lib/gc_async_mut/gpu/browser_engine/html_parser_gpu_flat_spec.spl`
→ `Results: 24 total, 24 passed, 0 failed`.


## 7. `awk_tool.spl` repaired (follow-up landed)

The five `_exec_action` call sites recorded in §4 are fixed. Establishing intent
first, as §4 required:

**What the 8th parameter is for.** `vars: [(text, text)]` is the awk *user
variable environment* — an association list of (name, value) pairs for variables
the program itself creates (`sum`, `n`, `t`). awk semantics require that
environment to survive across records and be readable in `END`; it therefore
cannot be function-local to `_exec_action` and must be passed in and handed back.

**What the tuple return represents.** `(i32, [(text, text)])` is
`(ctrl, updated_vars)`. `ctrl` is the control signal the action sends back to the
record loop — `1` means the action executed `next` (stop evaluating later rules
for this record). `.1` is the environment after the action ran, which the loop
must store so the following record and the `END` block observe it. Both halves
are load-bearing; binding the pair as a bare `i32` discarded the environment and
made `ctrl == 1` compare an `i32` against a tuple.

**What the sentinel was doing at runtime — not inert.** The awk tool is reached
through `BufferingTerminal`, whose constructor is an unresolved external symbol
in the JIT, so the whole module is dropped to the interpreter
(`[jit-fallback] unresolved external symbol 'BufferingTerminal_dot_new'`). The
interpreter *does* enforce arity at argument-binding time (§2d), so the missing
`vars` never became sentinel 3 on this path at all — it raised
`semantic: function expects argument for parameter 'vars', but none was provided`
and aborted the call. Measured at the origin tip `ab01e7808cd`, the existing
`test/01_unit/os/shell/awk_spec.spl` therefore reported:

```
Results: 28 total, 0 passed, 28 failed
```

Every one of the 28 examples failed with that message. **The awk tool was
completely non-functional**, and had been silently so: nothing in CI surfaced it.
The sentinel-3 corruption described in §1 is what this *would* do on any call
path that stays in the JIT (e.g. a real `Terminal` rather than the test double),
where `vars` is padded with tagged nil and no diagnostic is emitted at all.

**Three helper functions the file called were defined nowhere.**
`_resolve_multi_expr`, `_exec_printf` and `_exec_assign` were called from
`_exec_action` but had no definition in the repository. The arity defect masked
them: execution never got past the first `_exec_action` call, so the missing
definitions never had a chance to fail. They are implemented here in the file's
existing idiom, which is what makes the repaired call paths assertable at all.

### Changed

- `src/os/tools/shell/awk/awk_tool.spl`
  - `tool_awk` declares `var vars: [(text, text)] = []` and threads it through all
    five `_exec_action` calls (BEGIN, piped-stdin loop, `-` loop, file loop, END),
    binding `.1` back into `vars` and testing `.0` for the control code. END's
    returned environment is deliberately discarded — nothing runs after it.
  - Implemented `_resolve_multi_expr`, `_exec_printf`, `_exec_assign`, plus the
    small helpers they need (`_var_get`, `_var_set`, `_split_top_commas`).
  - `_resolve_expr` gained the `vars` parameter so `print sum` resolves a user
    variable, and an explicit `$NF` branch (`"NF".to_i32()` was yielding 0).
  - `_pattern_matches` / `_eval_nr_expr` replace the bare
    `line.contains(pattern)` test, which could never match the `NR_EXPR:` and
    `!`-negation patterns `_extract_rules` actually produces. These failures were
    invisible before because the spec could not run.
  - `ctrl == 2` now reports an unsupported statement, so an unparseable program
    exits nonzero instead of silently succeeding. This uses the control channel
    that the tuple repair restored.
- `src/os/apps/shell/_ShellApp/run_loop.spl:376` — **a sixth call site of the same
  family, found while verifying**: `tool_awk(self.vfs, self.cwd, args, self.terminal)`
  passed 4 arguments to a 5-parameter `tool_awk`, leaving `input: text` unbound;
  the shell's `awk` command then ran `input.len()` on it. Now passes `""`
  explicitly (the interactive dispatch has no piped-stdin plumbing to supply).
- `test/01_unit/os/shell/awk_spec.spl` and `test/unit/os/shell/awk_spec.spl`
  (kept byte-identical) — added test group 8, "awk action state threading",
  pinning the `(ctrl, vars)` contract with concrete values. Also repaired three
  defects in the spec itself: it imported `AckProgram`, a name defined nowhere;
  `"{ print }"` was parsed by Simple as *interpolation of a variable named
  `print`*, not as awk source; and three assertions were written
  `code.to_equal(0)` without `expect(...)`, so they asserted nothing.

### Verification

| state | verdict |
|---|---|
| pristine origin tip `ab01e7808cd` | `Results: 28 total, 0 passed, 28 failed` |
| repaired | `Results: 35 total, 35 passed, 0 failed` |
| sabotage A — one call site back to 7 args | `Results: 35 total, 4 passed, 31 failed` |
| sabotage B — tuple bound as bare `i32` again | `Results: 35 total, 26 passed, 9 failed` |
| restored | `Results: 35 total, 35 passed, 0 failed` |

Sabotage A reproduces the original error verbatim,
`semantic: function expects argument for parameter 'vars', but none was provided`.
Sabotage B fails exactly the nine examples that depend on `.0`/`.1` — the three
accumulation examples, the unsupported-statement exit, and the five state-threading
examples — and leaves the other 26 green, which is the targeting the group was
written for.

**`SIMPLE_STRICT_VREG` note.** The codegen arity warning quoted in §2c is emitted
from the Cranelift lowering, so it can only fire for code that stays in the JIT.
This module is dropped to the interpreter before codegen, so the warning is not
the operative signal here; the interpreter's hard arity error is, and it is what
both the baseline and sabotage A show. Static confirmation that no bad site
remains: all five `_exec_action` calls now pass 8 arguments and no 7-argument
call remains in the file.
