# Scoping: Cranelift JIT lambda/closure ABI defect

Status: DUPLICATE of jit_closure_abi_refuses_lambdas_and_miscompiles_fn_refs_2026-08-06.md
Status re-verified 2026-08-17 by source inspection (triage shard 02).
fix requires; it does not change any source file.

Baseline: `src/compiler_rust/compiler/src/codegen/jit.rs` and
`src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs` are
byte-identical to `refs/land/tip` (`eb5be9277e7`) at scoping time — `git diff
refs/land/tip -- <both files>` is empty. HEAD (`76e43b18741`) differs from
`refs/land/tip` only in unrelated files (interpreter/memstat/browser-hardening
work from other sessions); those diffs do not touch the closure/JIT code
discussed here. The concurrent-edit caution in the task brief (a removed
`lookup_name.contains('.')` guard) does not apply to the current working copy —
no such diff exists against origin for these files.

## 1. Confirmed current behaviour (binary evidence)

Binary built fresh for this scoping pass:

```
cargo build -p simple-driver
```

- Binary: `src/compiler_rust/target/debug/simple`
- Build log: `/tmp/jit_lambda_scoping/cargo_build.log` (`Finished dev profile
  ... EXIT:0`)
- **mtime: 2026-07-29 03:22:38 UTC**, 481,366,616 bytes

Three one-construct probes, `SIMPLE_JIT_TRACE_ADDR=1`, captured to files, `$?`
read from the command under test (not a pipe), 30s hard timeout:

| Probe | File | `[jit-addr]` lines? | Output | `$?` |
|---|---|---|---|---|
| Non-lambda fn call | `probes/no_lambda.spl` | **yes** — `double`, `main` both compiled | `42` | 0 |
| `arr.map(fn(x): x*2)` | `probes/lambda_map.spl` | **no** — guard fires | `[2, 4, 6]` (correct, interpreted) | 0 |
| Direct lambda call `f(4)` where `f = fn(x)->x*10` | `probes/lambda_direct_call.spl` | **no** — guard fires | `40` (correct, interpreted) | 0 |

Guard message observed verbatim on both lambda probes:

```
[INFO] JIT compilation failed, falling back to interpreter: Cranelift JIT compile: Module error: function 'main' creates a lambda/closure; the JIT closure ABI does not tag-box lambda arguments or results and is incompatible with the runtime's RuntimeClosure layout, so JIT would return wrong values or crash; deferring to interpreter
```

This confirms `8b72b34f005`'s guard (`jit.rs:111-118`,
`first_lambda_function_impl` at `jit.rs:196-209`) is live and correctly
demotes every lambda-containing module to the interpreter, and that the
interpreter path gives correct answers. Non-lambda modules still JIT normally
(`[jit-addr]` lines present, correct output). Raw logs:
`/tmp/jit_lambda_scoping/out_{no_lambda,lambda_map,lambda_direct}.log`.

## 2. Root cause, precisely located

### 2a. Closure object has no `HeapHeader`
`compile_closure_create` (`codegen/instr/closures_structs.rs:168-264`):
allocates via `rt_alloc(closure_size.max(16))` and stores the raw function
address at offset 0, captures at their offsets. **No `HeapHeader` is written
anywhere in this function.** The runtime's real closure constructor,
`rt_closure_new` (`runtime/src/value/objects.rs:177-194`), *does* write
`HeapHeader::new(HeapObjectType::Closure, size)` — but `compile_closure_create`
never calls it. Notably, `rt_closure_new` is **already declared as a JIT
runtime symbol** (`codegen/runtime_sffi.rs:525`,
`RuntimeFuncSpec::new("rt_closure_new", &[I64, I32], &[I64])`) — the plumbing
to call it exists and is registered, it is simply never emitted from
`compile_closure_create`. That lowers the size of fix #1 below.

### 2b. Indirect call boundary is untagged
`compile_indirect_call` (`closures_structs.rs:266-295`): loads the raw fn
pointer from offset 0 and calls it as
`fn(closure_ptr: i64, arg0, arg1, ... ) -> raw_result` using
`type_id_to_cranelift(param_ty)`/`type_id_to_cranelift(return_type)` — the
**native** (unboxed) type, not a tag-boxed `RuntimeValue` (i64). Neither the
`args` nor the `dest` result go through the tag-boxing helpers used elsewhere
in codegen (see `widen_struct_field_value` in the same file for the analogous
struct-field pattern, which does *not* apply here since this path doesn't call
it). This is why the task brief's two observed failure modes hold:
`fn(x: i64) -> i64: x * 10` applied to 4 returns a raw `40` consumed as a
tagged value (`>> 3` on read == `5`), and a raw `bool` `1` result aliases
`TAG_HEAP` with a NULL payload → SIGSEGV on first deref.

### 2c. Runtime helpers require the header `compile_closure_create` never writes
`rt_closure_func_ptr` (`runtime/src/value/objects.rs:227-230`) is
`get_typed_ptr::<RuntimeClosure>(closure, HeapObjectType::Closure)` — it
returns NULL unless the header tag matches. Exactly **three** call sites
consume a JIT-built closure through this gate (grepped
`rt_closure_func_ptr(` across `runtime/src/`, excluding its own
`pub extern` decl and unit tests):
- `rt_array_filter` (`collections.rs:3208-3229`)
- `rt_array_find` (`collections.rs:3233-3249`)
- `rt_option_map` (`objects.rs:355ff`, used for `Option.map` and, per its own
  comment, arrays too)

All three are already correctly declared `[I64, I64] -> [I64]` in
`runtime_sffi.rs` (`rt_array_filter` line 251, `rt_array_find` line 252,
`rt_option_map` line 540) — small blast radius on the runtime-consumer side.

### 2d. `rt_array_any`/`rt_array_all` are a *second, independent* defect
`rt_array_any`/`rt_array_all` (`collections.rs:3685-3745`) take **one**
argument (the array) and mean "are any/all elements truthy" — they never look
at a predicate closure and are correct for the interpreter's argument-less
`.any()`/`.all()` idiom. They are **not present in `runtime_sffi.rs` at all**
(grepped `RuntimeFuncSpec::new("rt_array_any"` /
`RuntimeFuncSpec::new("rt_array_all"` — zero hits).

But the interpreter's `.any(pred)`/`.all(pred)` **do** accept and apply a
predicate closure (`interpreter_method/collections.rs:215-236`,
`eval_array_any`/`eval_array_all`). Codegen maps the method name flatly to the
truthy-only runtime function regardless of arity —
`"any" => "rt_array_any"`, `"all" => "rt_array_all"` in both
`closures_structs.rs:1358-1359` and `instr/calls.rs:3249-3250` — with no
arity check. Because `rt_array_any`/`rt_array_all` aren't in
`runtime_sffi.rs`, a predicate-form call falls through to the "on-demand
declaration" branch in `calls.rs:3263-3282`, which declares a signature sized
by `args.len()` (2, for `receiver + closure`) against a Rust function that
only takes 1 argument — an ABI-mismatched import, silently dropping the
predicate and reducing `.any(pred)`/`.all(pred)` to plain truthiness. Because
constructing the predicate is itself a `ClosureCreate`, this path is currently
**unreachable** in JIT — it's masked by the same `8b72b34f005` guard — but it
must be fixed alongside the closure ABI, or removing the guard would trade one
correctness bug (fallback to interpreter) for a silent one (wrong `.any`/`.all`
results under JIT).

### 2e. Capture semantics — likely NOT an added axis of risk
Interpreter lambda capture (`interpreter_eval.rs:157-170`,
`call_value_with_args` on `Value::Lambda`) clones the captured `Env`
(`value.rs` `CowEnv`, `Env = CowEnv` alias at `value.rs:793`). `CowEnv`'s
`base` is `Option<Arc<HashMap<String, Value>>>` — an immutable, already-shared
snapshot — with a private `overlay` for local writes. Cloning a `CowEnv`
therefore captures a **value snapshot** of visible bindings at closure-creation
time (mutations after creation to the *original* frame's overlay are not
visible inside the clone; a captured heap-backed `Value`, e.g. an array, still
shares the underlying allocation, so contents mutations are visible the way
you'd expect from capturing a reference-counted object). The JIT's
`compile_closure_create` also snapshots: it reads each capture's `VReg` value
at the `ClosureCreate` instruction site and stores it into the closure block
once. **These appear to already match** (value-snapshot-at-creation in both
engines) — capture semantics are probably not additional scope beyond
tag-boxing. This can only be empirically confirmed once real closures compile
under JIT (the guard currently makes it impossible to observe JIT closure
behavior at all), so treat as "low risk, verify in the test plan below," not
as a closed question.

## 3. LLVM AOT backend has the identical defect, with **no guard at all**

Out of this task's stated scope (Cranelift JIT) but material to the risk
picture: `codegen/llvm/functions/objects.rs:218ff`
(`compile_closure_create`) and `codegen/llvm/functions/calls.rs:2570ff`
(`compile_indirect_call`) implement the same pattern — bare `rt_alloc`, raw
function-pointer store at offset 0, no `HeapHeader`. Grepped for an
LLVM-side equivalent of the `8b72b34f005` guard (`ClosureCreate` /
"refuse to compile" / "deferring" in the LLVM backend directory): **zero
hits**. AOT-compiled Simple binaries that use lambdas are apparently exposed
to the same miscompile today, with no interpreter fallback available at all
(AOT has no interpreter to fall back to). This is not something to fix under
this task, but the future implementer/reviewer should decide explicitly
whether the real fix lands in a shared helper both backends call, or is
duplicated — and whether the LLVM path needs its own stopgap guard (reject the
build, or emit a diagnostic) in the interim.

## 4. Enumerated sub-tasks for a real fix

1. **Emit real closure objects.** Change `compile_closure_create`
   (`closures_structs.rs:168`) to call the already-registered
   `rt_closure_new(func_ptr, capture_count)` runtime symbol instead of raw
   `rt_alloc`, so the object carries `HeapObjectType::Closure` in its
   `HeapHeader`. Captures still need per-offset stores after
   (`rt_closure_new` only allocates + zeroes); consider whether to also route
   captures through `rt_closure_set_capture` for tag-consistency instead of a
   direct offset store into `RuntimeClosure`'s capture array — check that
   `RuntimeClosure`'s field layout (`objects.rs:12-21`: `header, func_ptr:
   *const u8, capture_count: u32, reserved: u32, [captures...]`) is what
   `capture_offsets` in the MIR instruction already assumes, or whether MIR's
   offsets were computed against the old bare-`rt_alloc` layout and need
   re-deriving.
2. **Tag-box the indirect-call boundary.** `compile_indirect_call`
   (`closures_structs.rs:266`) must box each argument to a `RuntimeValue`
   (i64) before the call and unbox/interpret the tagged result afterward,
   matching how ordinary (non-indirect) calls already box/unbox at their call
   sites elsewhere in this codegen (grep `type_id_to_cranelift` callers plus
   whatever tag-box helper regular calls use — this file's own
   `widen_struct_field_value` is the nearest analog but is for struct-field
   storage, not call args, so verify against the ordinary direct-call path
   before reusing it).
3. **Fix `.any(pred)`/`.all(pred)`.** Either (a) add real predicate-taking
   runtime functions (e.g. `rt_array_any_by`/`rt_array_all_by`, mirroring
   `rt_array_filter`'s `(array, closure) -> result` shape and going through
   `rt_closure_func_ptr`), register them in `runtime_sffi.rs`, and make
   codegen dispatch on arity (0 args → `rt_array_any`/`rt_array_all` truthy
   form; 1 arg → the new predicate form) in both
   `closures_structs.rs:1358-1359` and `calls.rs:3249-3250`; or (b) confirm
   with the language spec that `.any()`/`.all()` are meant to be argument-less
   only and reject a closure argument at HIR/type-check time, deleting the
   interpreter's predicate-taking behavior instead. (a) matches current
   interpreter behavior and existing test surface; (b) is a smaller diff but a
   possibly-breaking language change. **Recommend (a)** — don't change
   accepted syntax mid-cleanup.
4. **Verify `capture_offsets` layout end-to-end** against `RuntimeClosure`
   once `rt_closure_new` is wired in (sub-task 1) — this is the one place a
   "smaller than feared" outcome could hide: if MIR already computes offsets
   consistent with `RuntimeClosure`'s post-header layout, sub-task 1 could be
   a same-file two-function patch with no MIR/HIR change at all.
5. **LLVM AOT parity decision** (see §3) — explicitly out of this task, flag
   for follow-up: fix once in a shared helper, duplicate the fix, or add an
   interim reject-guard on the LLVM path mirroring `8b72b34f005`.

## 5. Blast radius and risk

- **Codegen surface changed:** 2 functions, 1 file
  (`compile_closure_create`, `compile_indirect_call` in
  `closures_structs.rs`) — genuinely 1 implementation each. Confirmed 2 call
  sites per function, but both are dispatch shims onto the same
  implementation, not independent logic: `codegen/instr/mod.rs:732,751` is the
  direct MIR-instruction-loop dispatch, and `codegen/cranelift_emitter.rs:
  177,359` (`emit_indirect_call`/`emit_closure_create`) is a thin trait-method
  forwarder that immediately calls the same two functions with the same
  arguments. Fixing the two `closures_structs.rs` functions fixes both call
  paths.
- **Runtime consumer surface:** exactly 3 functions gated on
  `HeapObjectType::Closure` (`rt_array_filter`, `rt_array_find`,
  `rt_option_map`) — small, already correctly declared in `runtime_sffi.rs`.
- **New/changed runtime surface for sub-task 3:** 0-2 new `extern "C"` fns
  (`rt_array_any_by`/`rt_array_all_by`) plus 2 `runtime_sffi.rs` entries plus
  arity-dispatch edits in 2 codegen files.
- **Staging is possible.** The guard in `jit.rs` trips on *any* `ClosureCreate`
  in a module, so it cannot be narrowed by construct today — but the fix
  itself can be staged: land sub-tasks 1+2+4 (closure objects + tag-boxing)
  first, verify `map`/`filter`/`find`/direct-lambda-call correctness, *then*
  land sub-task 3 (`any`/`all` predicates) as a follow-up, keeping the
  `8b72b34f005` guard narrowed (not removed) to only demote modules using
  `.any(pred)`/`.all(pred)` until sub-task 3 lands. That requires the guard's
  `first_lambda_function_impl` to become predicate-aware (walk for
  `ClosureCreate` feeding specifically into an `any`/`all` call) rather than
  "any `ClosureCreate` at all" — a small, separate change to `jit.rs` gating
  logic.
- **Removing the guard mid-way is dangerous.** If sub-tasks 1+2 land but the
  guard is deleted before sub-task 3, `.any(pred)`/`.all(pred)` silently
  regress from "correct via interpreter" to "wrong via JIT" (predicate
  dropped, truthy-only result) — exactly the failure class `8b72b34f005` exists
  to prevent. The guard must stay (in full or narrowed form) until every
  closure-consuming runtime helper is verified, not just until `map`/`filter`
  look right.
- **Not this task's blast radius but adjacent:** LLVM AOT backend (§3) shares
  the closure-object defect with no safety net; SIMD/GC treatment of a
  `HeapObjectType::Closure` object once headers exist (tracing/free paths —
  `rt_closure_free` exists at `objects.rs:234-244` and is unaffected, but
  confirm no GC-side path assumes closures are headerless today).

## 6. Recommended sequencing

1. Sub-task 4 first (read-only): confirm or refute the `capture_offsets`
   layout question — this alone could downgrade the whole effort from
   "coordinated closure-representation change" to "swap `rt_alloc` for
   `rt_closure_new`, done," which is the best-case outcome the task brief asks
   to flag if found. (Not confirmed in this pass — left as the first concrete
   step for the implementer, since it requires reading MIR lowering for
   `ClosureCreate`'s offset computation, out of scope for a scoping-only pass.)
2. Sub-tasks 1 + 2 together (they're two functions in the same file, and #2
   can't be tested independently of #1 producing a valid closure object).
3. Narrow the `8b72b34f005` guard to `.any`/`.all`-with-predicate only (small
   `jit.rs` change), so `map`/`filter`/`find`/direct-call lambdas start
   JIT-compiling while `.any(pred)`/`.all(pred)` still safely demote.
4. Sub-task 3 (`any`/`all` predicate runtime functions + arity dispatch).
5. Remove the narrowed guard entirely once sub-task 3's probes pass.
6. File the LLVM AOT follow-up (§3) as its own bug, independent of this
   sequencing.

## 7. Test plan for the future implementer

One construct per probe file, both engines, `SIMPLE_JIT_TRACE_ADDR=1` to prove
JIT actually ran (not silently demoted), `$?` from the command under test, hard
timeout, real binary built fresh with mtime stated — same method used in §1.

| # | Construct | Assert |
|---|---|---|
| 1 | `f = fn(x: i64) -> i64: x * 10; f(4)` | JIT compiles (`[jit-addr]` for the lambda body + `main`); result `40` |
| 2 | `f = fn(x: i64) -> bool: x > 1; f(4)` | JIT compiles; result `true`, no SIGSEGV (regression probe for the exact crash named in `jit.rs`'s guard comment) |
| 3 | `[1,2,3].map(fn(x): x * 2)` | JIT compiles; `[2, 4, 6]` |
| 4 | `[1,2,3].filter(fn(x): x > 1)` | JIT compiles; `[2, 3]` |
| 5 | `[1,2,3].find(fn(x): x > 1)` | JIT compiles; `2` |
| 6 | `Some(3).map(fn(x): x + 1)` | JIT compiles; `Some(4)` |
| 7 | `[1,2,3].any(fn(x): x > 2)` | Correct (`true`) under whichever engine currently handles it (interpreter until sub-task 3 lands; JIT after) — regression probe for the arity-drop defect in §2d |
| 8 | `[1,2,3].all(fn(x): x > 0)` | Correct (`true`), same caveat as #7 |
| 9 | Closure capturing a mutable outer local, called after the outer local changes | Compare interpreter vs JIT result — resolves the open capture-semantics question in §2e |
| 10 | Nested lambda (lambda returning a lambda) | Both engines agree — not explicitly analyzed in this scoping pass, flag as untested surface |
| 11 | Multi-arg lambda `fn(x, y): x + y` used as `.reduce`/other 2-arg callback if the language exposes one | ABI check beyond the 1-arg cases this scoping pass probed |

Run every probe under `SIMPLE_JIT_STRICT=1` too, to make sure no case
silently re-demotes without the strict-mode hard failure firing when it
shouldn't (or does fire when it should, for any residual gap the fix doesn't
close).

## Evidence files (not committed)
- `/tmp/jit_lambda_scoping/cargo_build.log` — build log, exit 0
- `/tmp/jit_lambda_scoping/probes/{no_lambda,lambda_map,lambda_direct_call}.spl` — probe sources
- `/tmp/jit_lambda_scoping/out_{no_lambda,lambda_map,lambda_direct}.log` — captured run output
- `/tmp/jit_lambda_scoping/run_summary.log` — exit codes for the three runs

## Blocker discovered 2026-07-29 — `rt_closure_new` not declared as a runtime import

A partial lambda-ABI lane wired `compile_closure_create`
(`codegen/instr/closures_structs.rs`) to call the HeapHeader-carrying
constructor `rt_closure_new`, and added a jit.rs guard hook. On rebuild, every
lambda probe still **demoted** — but now with a hard panic instead of clean
demotion:

```
missing runtime fn 'rt_closure_new' in main
  location=compiler/src/codegen/instr/helpers.rs:396:28
```

Root cause: `resolve_runtime_func` (`codegen/instr/helpers.rs:391`) looks the
name up in `ctx.func_ids` then `ctx.runtime_funcs`, and panics on miss. The
lambda codegen *emits a call* to `rt_closure_new` but the symbol is **never
declared** in the runtime-import table that populates `ctx.runtime_funcs`. So
the second table the lambda fix must update is that runtime-import declaration
list (same place the other `rt_*` closure/collection runtime fns are declared),
not just `compile_closure_create` + the jit.rs guard.

**Required for the next lambda lane (three edits, not two):**
1. `compile_closure_create` → call `rt_closure_new` (HeapHeader ctor). [done in salvage]
2. jit.rs guard → stop blanket-demoting `ClosureCreate`. [done in salvage]
3. **Declare `rt_closure_new` in the runtime-import table** so
   `resolve_runtime_func` resolves it. [MISSING — this is the blocker]

Until all three land together, the correct resting state is the reverted
origin version (blanket `ClosureCreate` guard → lambdas run correct-via-demotion
on the interpreter, no panic). The partial 3-of-3-minus-one work is snapshotted
at `/tmp/salvage_0729/{closures_structs.rs.lane,jit.rs.lane}` — do NOT land it as
is; it panics.
