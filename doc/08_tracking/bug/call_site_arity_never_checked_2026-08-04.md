# Call-site argument count is never checked before codegen (2026-08-04)

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
census found 7 real sites, all repaired (`af0fdf192d8`, `7788bdf1d56`, §7). §8
then measured the **cross-module** population §3 had declared unmeasured and
found **154 real sites**; §9 repairs 26 more of them across three modules, and
lists what stays open — a 96-site `wine_vm_commit/4` cluster and a 9-site
`dyn_torch_tensor_*` cluster, neither of which can be proved by value in a
call-site lane. Detection itself remains open per §5.
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

## 8. Cross-module census — §3's "unmeasured" population, measured

§3 measured only *same-file* free-function calls and said explicitly that
cross-module calls were unmeasured. They are measured here. The census was
validated against ground truth **before** any of its other output was believed:
run against `64319777883` (the parent of `7788bdf1d56`) it independently
rediscovers exactly the six sites that commit repaired — five `_exec_action`
calls in `awk_tool.spl` and the `tool_awk` call at `run_loop.spl:376` — and
nothing else from those two files.

### Method

Two stages, both re-runnable (`.shs` driver + `.spl` argument counter):

1. **Index** every module-level `fn name(` / `fn name<` declaration in owned
   `src/` and `test/` (`vendor/` excluded per CLAUDE.md Owned-Code Scope).
2. **Resolve.** A bare `name(...)` is only attributed to a declaration when the
   name is declared exactly **once** corpus-wide *and* collides with no method
   name (`me` / `static fn`), no nested `fn`, and no class/struct/enum/trait/
   actor/mixin name — a constructor call is syntactically identical to a free
   call. Then, per call site, the declaration must be either in the **same
   file** or named in a `use`/`import` line **whose module token is the
   declaring file's own module**. Anything else is `UNBOUND` and dropped.
3. **Count** arguments with a balanced scanner that honours string literals,
   `#` comments, char literals, trailing commas, `\p:` inline-lambda parameter
   commas, `x |> f(a)` pipe desugaring, and — on the declaration side —
   defaulted parameters, varargs, generic `<…>` commas, and `->` arrows.

### Numbers

| stage | count |
|---|---|
| module-level `fn` declarations indexed | 119,244 |
| names declared exactly once | 58,972 |
| names surviving collision + parse filters | 56,073 |
| bare call sites arity-checked | 237,215 |
| multi-line calls, **not** measured | 5,911 |
| raw mismatch candidates | 1,012 |
| → dropped `UNBOUND` (callee not visible at the call site) | 555 |
| → dropped `DOCSTRING` (inside a `"""…"""` prose block) | 294 |
| **resolved candidates** (`IMPORTED` 154 + `SAMEFILE` 9) | **163** |

**False-positive rate 83.9%** at the raw stage (849 of 1,012), which is why the
raw number must never be quoted. Of the surviving 163, nine more are known
false positives on inspection — five intentional `test/fixtures/
concurrency_api_misuse/*_wrong_arity.spl` negative fixtures, two AOP pointcuts
(`on pc{ execution(* hart64_step_body(..)) }`), and two `>>>` doc examples in
`threads.spl`. **154 are real.**

The single largest filter was requiring the caller to actually import the
callee's *module*, not merely a symbol of that name. A name-only import check
admitted, for example, `muldiv_execute` in `rv32_muldiv_spec.spl` (imported from
`hardware.rv32imac.ext.rv32_muldiv`, matched against a declaration in
`rv64gc_rtl/mul_div.spl`) and `detect_content_type` in `resource_loader_spec.spl`
(imported from `browser_engine.resource_loader`, matched against
`web_framework/form_parser.spl`) — 98 and 28 phantom sites respectively.
Requiring the module token to match drops both. This is the same collision
mechanism that reduced the earlier "30 drifted trait pairs" census to 0.

### Ranked real mismatches

Blast radius is *interpreter* when the containing module drops out of the JIT —
those are already-broken code, since the interpreter enforces arity — and *JIT*
when it does not, where the missing argument is nil sentinel 3 and nothing is
reported at all.

| callee | sites | file(s) | radius | status |
|---|---|---|---|---|
| `_exec_action/8`, `tool_awk/5` | 6 | `awk_tool.spl`, `run_loop.spl` | interpreter | fixed `7788bdf1d56` |
| `be_dom_set_style/2` | 6 + 4 spec | `engine_merge.spl` | interpreter | fixed, see §9 |
| `glass_tokens_to_css/2` | 18 | `glass_css_output_spec.spl` | interpreter | fixed, see §9 |
| `build_tree_with_title/3` | 2 | `windows_compat_spec.spl` | interpreter | fixed, see §9 |
| `wine_vm_commit/4` | 96 | `wine_vm_adapter.spl` + 47 specs | interpreter | **real, NOT fixed** |
| `dyn_torch_tensor_{slice,sum_dim,mean_dim,min_dim,max_dim,argmin,argmax}` | 9 | `torch_ndarray.spl` | JIT | **real, NOT fixed** |
| `ifconfig/1` | 3 | `ifconfig_tool.spl`, `devinfo_tool.spl` | JIT | real, NOT fixed |
| `pbkdf2_sha256/4` | 4 | `crypto_reference_spec.spl` | blocked | real, NOT fixed |
| `compile_options_hash_compute/7` | 2 | `object_provider_spec.spl` | blocked | fixed (arity only), see §10.3 |
| `generate_csrf_token/2` | 2 | `csrf_spec.spl` | interpreter | real, NOT fixed |
| `verify_rv64_qemu_user_proof_contract/2` | 2 | `os_build_run.spl`, `qemu_runner_part2.spl` | JIT | real, NOT fixed |
| `read_log/3`, `gui_adapter_new/1`, `scv_export_git_fast_import/4`, `terminal_execute/2` | 4 | assorted `src/` | JIT | real, NOT fixed |

### Why the unfixed ones are unfixed

- **`wine_vm_commit/4` (96 sites, the largest cluster).** Every caller passes
  three arguments, putting the protection string where `size` belongs and
  leaving `protection` unset. It is real. But no spec in the family can be
  turned green by fixing arity alone: `wine_vm_adapter_spec.spl` is
  `11 total, 0 passed, 11 failed` on `semantic: function wine_vm_space_new not
  found`, and `wine_process_session_vma_thunk_write_spec.spl` is
  `5 total, 0 passed, 5 failed` on `class WineVmOpResult has no field named
  region` plus two more missing functions. Repairing arity there would be an
  unproven edit on top of a feature that is broken for three other reasons —
  it needs its own lane, not a call-site sweep.
- **`dyn_torch_tensor_*` (9 sites).** The callers pass a PyTorch-shaped
  `keepdim` flag (`sum_dim(h, dim, 0)`) and a slice `step`
  (`slice(h, 0, start, stop, step)`) that the SFFI signatures do not have. The
  `step` is silently discarded, so a strided slice quietly becomes contiguous.
  There is no spec for `torch_ndarray.spl` and the path needs a live torch
  runtime, so no value-level proof is available; deciding whether to widen the
  SFFI ops or narrow the callers is a torch-lane call.
- **The remaining `src/`-only singletons** have no spec that reaches them, so a
  fix could not be proved by value. They are listed above rather than edited on
  a guess.

### Coverage limits of this census (a floor, not the answer)

Still unmeasured: **multi-line calls** (5,911 sites skipped), **method calls**
(`me` / `static fn`, excluded wholesale because a bare-name census cannot
resolve a receiver), **named-argument calls**, and every call whose callee name
is declared more than once (58,972 of 119,244 declarations are *not*
unique-by-name, so roughly half the free-function population is outside the
resolvable set). An AST-level check inside the compiler — i.e. re-arming
`fill_call_defaults` once `_FlatAstBridge` stops hardcoding `has_default:
false`, per §5 — remains the only way to cover those.

## 9. Three further instances repaired from the §8 census

All three failed the same way as `awk_tool.spl`: the containing module reaches
the interpreter, which *does* enforce arity (§2d), so the code was not silently
corrupt — it was dead. Each was verified red→green by value and sabotage-
verified back to red with the original message, in a pristine worktree.

**`be_dom_set_style/2` — `src/app/ui.chromium/engine_merge.spl` (`9a7812edd8d`).**
Called as a CSS property setter, `be_dom_set_style(node, "width", "256px")`, at
six sites in the module and four more in the spec; `dom_accessors.spl` has no
such `(node, prop, value)` accessor. Repaired onto the canonical
read-modify-write idiom `widget_to_dom.spl` already uses. `StyleProps.width`/
`height` are f64 px, so the `"320px"` texts the builders accept are now parsed
by `engine_merge_css_px` instead of being handed to a text field.

    before  Results: 7 total, 1 passed, 6 failed
    after   Results: 7 total, 7 passed, 0 failed
    sabotage (one 3-arg call restored)
            Results: 7 total, 2 passed, 5 failed
            semantic: function expects 2 argument(s), but more were provided

**`glass_tokens_to_css/2` — `test/{unit,01_unit}/lib/common/glass_css_output_spec.spl`
(`9afe3c28c06`).** Called with one argument at all 18 sites; the one production
caller (`glass_css.spl:129`) already passes both. `StitchMetadata.glass()` is
what `glass_css.spl`'s own dispatch pairs with the default glass theme.

    before  Results: 29 total, 11 passed, 18 failed
    after   Results: 29 total, 29 passed, 0 failed
    sabotage (second argument dropped at line 54)
            Results: 29 total, 28 passed, 1 failed
            semantic: function expects argument for parameter 'sds', but none was provided

**`build_tree_with_title/3` — `test/{unit,01_unit}/app/ui/windows_compat_spec.spl`
(`2a4236e13d4`).** Called with two arguments; all five production callers in
`src/os/desktop/shell_ui_builders.spl` already pass `"dark"`.

    before  Results: 34 total, 33 passed, 1 failed
    after   Results: 34 total, 34 passed, 0 failed
    sabotage (theme argument dropped)
            Results: 34 total, 33 passed, 1 failed
            semantic: function expects argument for parameter 'theme', but none was provided

Command form for all of the above:
`bin/simple test <spec> --no-cache --no-cover-check`, verdict read from the
`^Results:` line of a captured log (it is otherwise buried under lint output).

## 10. §8's remaining ranked clusters, worked (2026-08-10)

Six clusters from §8's ranked table were investigated in order. One was
landed (partially — the arity defect itself is fixed and proven, but the
spec cannot reach full green for an unrelated pre-existing reason). The rest
are real defects left untouched, each for a documented reason — either a
deeper feature gap that an arg edit cannot repair, or no spec reaches the
call at all so a fix could not be proven by value.

### 10.1 `ifconfig/1` — NOT fixed, deeper than arity

`src/os/userlib/net.spl:126` — `fn ifconfig(if_index: u32) -> Result<NetIfInfo, text>`
returns info for **one** interface selected by index. All three callers
(`src/os/tools/net/ifconfig_tool.spl:17,34`, `src/os/tools/dev/devinfo_tool.spl:58`)
call `ifconfig()` with zero arguments and iterate the result as a **list**
(`for iface in ifaces`). The mismatch is not just a missing argument — the
return *type* is wrong for how every caller uses it (`Result<NetIfInfo, text>`
vs. an expected `[NetIfInfo]`). Making this callable would require a real
enumerate-all-interfaces feature (loop over indices until a NOT_FOUND result,
or a new syscall), not a call-site argument. No spec in the repo reaches
`ifconfig_tool.spl` or `devinfo_tool.spl` (`grep` for `ifconfig_tool\|devinfo_tool\|run_ifconfig`
under `test/` returns nothing), so there is also no value-level way to prove
any fix. Left open.

### 10.2 `pbkdf2_sha256/4` — NOT fixed, symbol doesn't exist

`test/01_unit/lib/crypto/crypto_reference_spec.spl:6` imports
`pbkdf2_sha256, pbkdf2_sha512, pbkdf2_with_algorithm, get_recommended_pbkdf2_iterations`
from `std.crypto.pbkdf2`. That module
(`src/lib/crypto/pbkdf2.spl`) re-exports only `pbkdf2_sha256_bytes`,
`pbkdf2_sha384_bytes`, `pbkdf2_sha512_bytes` from
`std.common.crypto.pbkdf2` (`src/lib/common/crypto/pbkdf2.spl`) — none of the
four imported names exist anywhere in that module. This is not a call-site
arity slip at all: the callee the spec wants was never implemented (a
text-in/text-out convenience wrapper around the byte-array API, plus an
algorithm-selection dispatcher and a recommended-iteration-count constant).
Fixing it means writing three new functions, which is feature work outside a
call-site-only lane. Left open — matches the doc's existing "blocked" radius
label in §8's table.

### 10.3 `compile_options_hash_compute/7` — FIXED (partially provable), `1c1a6a0...`

`src/compiler/80.driver/cache/compile_options_hash.spl:103` —
`fn compile_options_hash_compute(backend: text, opt_level: i64, release: bool, debug_info: bool, gc_off: bool, profile: text, allowed_families: [text]) -> CompileOptionsHash`.
Two spec-local helpers called it with only the first 5 positional arguments,
leaving `profile` and `allowed_families` unbound:

- `test/{01_unit,unit}/compiler/linker/fixed_backend_success_spec.spl:77`,
  `build_fixed_backend_smf()` — `compile_options_hash_compute("llvm", 3, true, false, false)`
- `test/{01_unit,unit}/compiler/linker/object_provider_spec.spl:25`,
  `mark_smf_as_pic_for_backend()` — `compile_options_hash_compute(backend, 2, true, true, false)`

Intent: every production caller (`driver_types.spl:338`, `smf_cache.spl:651`,
`watcher_client.spl:153`, `module_loader.spl:908`) passes `opts.profile` and
`opts.allowed_families` straight through from `CompileOptions`; there is no
special-cased "no profile / no family restriction" call anywhere. The
canonical unrestricted values are `"default"` (the profile literal used
throughout the driver, e.g. `compile_options_hash_spec.spl`'s whole suite)
and `[]` (no family filter). Fixed both spec-local call sites to
`compile_options_hash_compute(<same args>, "default", [])`.

**Verification — `fixed_backend_success_spec.spl` (the one spec whose arity
error is directly reachable):**

    RED  (pristine, 5-arg call)
         Results: 1 total, 0 passed, 1 failed
         semantic: function expects argument for parameter 'profile', but none was provided
    GREEN (7-arg call, "default", [])
         Results: 1 total, 0 passed, 1 failed
         semantic: method `to_bytes` not found on type `str` (receiver value: code)

The arity defect is conclusively fixed — the original error is gone and does
not recur under sabotage (reverting to the 5-arg call reproduces it verbatim).
But the spec cannot go green: `build_section_entry()` in the same file calls
`"code".to_bytes()` at line 53, and `text.to_bytes()` is not a resolvable
method under this test path — a **separate, pre-existing defect**, unrelated
to arity and out of this lane's scope (no `text.to_bytes` fix was made).
Recorded here rather than silently claimed as a full pass.

**`object_provider_spec.spl`** was fixed identically for consistency (same
callee, same missing arguments, same intended values), but its two `it`
blocks that reach `mark_smf_as_pic_for_backend()` were already RED for an
unrelated reason before and after the fix — `semantic: unknown static method
from_bytes on class SmfHeader` fires while parsing the SMF header, before
`compile_options_hash_compute` is ever called (`Results: 4 total, 2 passed, 2
failed`, byte-identical before and after). The arity call there is real but
currently dead code on every execution path a spec can reach; the fix is
correct (matches the callee signature and every real caller's intent) but not
independently provable by this spec. `test/01_unit/compiler/cache/compile_options_hash_spec.spl`
already calls the 7-arg form correctly throughout and continues to pass.

### 10.4 `generate_csrf_token/2` — NOT fixed, spec targets a nonexistent API surface

`test/unit/lib/http_server/csrf_spec.spl:20,25` call `generate_csrf_token()`
with zero arguments against
`src/lib/nogc_async_mut/http_server/csrf.spl:67` — `fn generate_csrf_token(config: CsrfConfig, session_id: text) -> text`.
A trial fix (constructing a `CsrfConfig` with a non-empty `secret_key` and a
session id) does eliminate that specific arity error under RED/GREEN
(`semantic: function expects argument for parameter 'config', but none was
provided` → gone), but the same spec file's other 8 examples (of 10 total)
fail with `semantic: function \`validate_csrf_token\` not found` and
`semantic: function \`is_csrf_exempt_method\` not found` — those two names,
and `default_csrf_config` that the file also imports, do not exist anywhere
in `csrf.spl`. This file is a stale duplicate of the current, correct
`test/01_unit/lib/http_server/csrf_spec.spl` (which already calls
`generate_csrf_token(config, "session-abc")` correctly and passes) written
against an older/aspirational API shape that was never implemented. Per the
task's methodology, the arity edit alone cannot make this spec pass (`Results:
10 total, 0 passed, 10 failed` before and, for the remaining 8 examples,
after), so **the trial fix was reverted** and nothing was changed here — left
open, matching the `pbkdf2_sha256` pattern of "callee never existed."

### 10.5 `verify_rv64_qemu_user_proof_contract/2` — NOT fixed, blocked two ways

`src/lib/hardware/riscv_common/core/riscv_formal.spl:103` —
`fn verify_rv64_qemu_user_proof_contract(code_start: i64, exit_code: i64) -> Result<text, text>`.
Both production call sites (`src/os/_QemuRunner/os_build_run.spl:813`,
`src/os/qemu_runner_part2.spl:682`, near-duplicate files) call it from inside
`verify_qemu_formal_output(arch: Architecture, output: text)` as
`verify_rv64_qemu_user_proof_contract(output)` — one `text` argument where the
callee wants two `i64`s. The wrapping function has no `code_start` in scope at
all, and `output` is raw QEMU stdout text, not a numeric exit code — turning
this into a real fix needs the wrapper to actually parse an exit code out of
`output` and know the code segment's base address, which is feature work, not
an argument fix. The one spec that calls the underlying function directly,
`test/01_unit/hardware/riscv_common/riscv_formal_contract_spec.spl:135`
(`verify_rv64_qemu_user_proof_contract(output)`, also 1-arg), cannot even be
used to prove a fix: it fails before execution reaches that line with
`semantic: Cannot resolve module: hardware.riscv_common.core.riscv_formal`
(`Results: 1 total, 0 passed, 1 failed`) — a pre-existing, unrelated module-path
defect. Left open on both grounds.

### 10.6 `read_log/3`, `gui_adapter_new/1`, `scv_export_git_fast_import/4`, `terminal_execute/2` — NOT fixed, unprovable (3 of 4) / blocked (1 of 4)

All four are real call-site arity mismatches with an obvious, low-risk
correct fix, but the task's methodology requires proving each fix by value,
and none can be:

- **`read_log/3`** (`src/os/userlib/log.spl:50`,
  `fn read_log(min_level: LogLevel, offset: u64, count: u32) -> Result<[KLogEntry], text>`).
  `src/os/tools/log/journal.spl:31`, `JournalReader.refresh()`, calls
  `read_log(self.offset)` — 1 arg. The obvious fix is
  `read_log(self.filter.min_level ?? LogLevel.Debug, self.offset, <some count>)`,
  mirroring `read_recent()`'s own `read_log(LogLevel.Debug, 0, count)` two
  lines below. No spec references `JournalReader` (`grep` under `test/` for
  `JournalReader` finds nothing related to this file); not touched.
- **`gui_adapter_new/1`** (`src/app/test_daemon/adapters/gui_adapter.spl:96`,
  `fn gui_adapter_new(mode: text) -> GuiAdapter`, which already tolerates an
  empty `mode` by falling back to `"headless"`). `src/app/test_daemon/daemon.spl:495`
  calls `gui_adapter_new()` — 0 args; `gui_adapter_new("")` is the obvious fix.
  No spec calls `test_daemon_start()`, the only caller of this line
  (`grep` for `test_daemon_start` under `test/` finds nothing); not touched.
- **`scv_export_git_fast_import/4`** (`src/lib/scv/fast_import.spl:217`,
  `fn scv_export_git_fast_import(root: text, stream_path: text, branch: text, since: text) -> text`).
  `src/lib/scv/public_remote.spl:61` calls it with 3 args, dropping `since`.
  Reading `scv_export_dag_commits()` (line 177-190), `since == ""` walks the
  full history to the root — the obvious fix is
  `scv_export_git_fast_import(root, "{out_dir}/export.fi", branch, "")`,
  matching `scv_public_export`'s intent to do a full export. No spec calls
  `scv_public_export` (`grep` for `scv_public_export` under `test/` finds
  nothing); not touched.
- **`terminal_execute/2`** (`src/lib/nogc_sync_mut/terminal/connection.spl:76`,
  `fn terminal_execute(conn: TerminalConnection, command: text) -> TerminalExecResult`
  — no timeout parameter exists anywhere in the implementation or its three
  backends, `ssh_terminal_execute`/`telnet_terminal_execute`/`relay_terminal_execute`).
  `src/app/test_daemon/adapters/remote_pc_adapter.spl:180` calls
  `terminal_execute(self.connection, cmd, timeout_ms)` — 3 args, expecting
  timeout enforcement that does not exist in the callee at any layer. Dropping
  `timeout_ms` would silently discard the caller's intent (same shape as the
  already-documented `dyn_torch_tensor_*` `step` truncation in §8) — this is a
  feature gap, not a call-site fix. Left open.

All six clusters are therefore accounted for: **one landed** (§10.3,
`compile_options_hash_compute/7`, arity-provably-fixed though the spec stays
red for an unrelated `text.to_bytes()` gap), **five left open** with the
specific reason recorded above.

## REPRODUCED 2026-08-17 (fleet lane C) — live, exit 0, no diagnostic

Probe re-run on the deployed binary, matching §1's probe exactly
(`f3(a,b,c) -> c*1000 + a*10 + b`):

```
RC=0
too_few=  3078      <- f3(7, 8)         one argument too FEW
too_many= 9078      <- f3(7, 8, 9, 11)  one argument too MANY
correct=  9078      <- f3(7, 8, 9)
```

Both malformed calls compile clean and exit 0. The too-many call silently DROPS the extra
argument. The too-few call silently fabricates `c`, yielding **3078 instead of 9078** — a
wrong number handed back with no error anywhere. Silent-corruption class confirmed live.

### The stated blocker is now STALE — re-arming is partly unblocked

`src/compiler/35.semantics/resolve.spl:815-822` suppresses the arity error with this reason:

> the lean bridge currently hardcodes `has_default: false`
> (`_FlatAstBridge/convert_nodes.spl:571/682`) ... Re-enable the arity error only after the
> bridge captures has_default faithfully.

That is no longer true. `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl` now
computes it for real at line 1730:

```
val p_has_default = p_default_idx >= 0
```

and line 1713 explicitly records that it *used to* hardcode `false` for every parameter. So
the bridge half of the precondition is MET.

### Why this lane did not arm it anyway

Two reasons, both evidence-based:

1. `has_default` is still hardcoded `false` at several HirParam construction sites OUTSIDE the
   bridge — `20.hir/hir_lowering/_Items/module_lowering.spl:236`,
   `_Items/declaration_lowering.spl:151` and `:381`. (`declaration_lowering.spl:586` does
   propagate `p.has_default` correctly, so the coverage is partial, not uniform.) Arming the
   error now would false-fire on whichever paths flow through the remaining hardcodes. Those
   files are under `20.hir/hir_lowering/**`, owned by another lane this session.
2. The defect above reproduces on the **Rust seed**, which does not execute the pure-Simple
   `35.semantics/resolve.spl` pass at all. A fix in `resolve.spl` therefore cannot be proven
   by the probe that demonstrates the bug — and an unprovable patch to a compiler pass that
   can false-fire is precisely the failure mode this queue exists to avoid.

Detection remains open per §5. Concrete next step for whoever picks this up: make
`has_default` faithful at the three `20.hir/hir_lowering` sites listed above, THEN re-arm the
error at `resolve.spl:815`, and prove it through the pure-Simple pipeline (not the seed).

## Verification 2026-08-17 (w0001 compiler_spl lane)

Row confirmed OPEN by current source. `src/compiler/35.semantics/resolve.spl`,
`fill_call_defaults` (~line 775), carries the disarm explicitly in-source at ~line 821:

```
# Arity-error half intentionally omitted (M12 3b). The lean
# bridge currently hardcodes `has_default: false`
# (_FlatAstBridge/convert_nodes.spl:571/682), so emitting a "too few
# arguments" error here would FALSE-FIRE on every valid
# omitted-default call. ...
# Re-enable the arity error
# only after the bridge captures has_default faithfully.
return filled
```

So the checker is not merely unwritten — it is written-and-deliberately-suppressed,
and the blocker is named: the lean bridge must capture `has_default` faithfully first.
**That is the real fix target, not `resolve.spl`.** No patch applied: arming the check
without the bridge fix would false-fire on every valid omitted-default call, which is a
worse regression than the bug. Prerequisite filed as the actual dependency.
