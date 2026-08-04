# Call-site argument count is never checked before codegen (2026-08-04)

**Status:** OPEN (detection not armed). Seven real in-tree call sites found; the
two unambiguous ones are fixed here, the remaining five (one function) are
recorded in §4 as a separate follow-up.
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

## 4. Not fixed here — `awk_tool.spl` signature drift (follow-up)

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
