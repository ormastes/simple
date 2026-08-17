# Dict `.set()` vs `d[k]=v` write parity -- 2026-08-07 re-verification

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 01).

## Status: FIXED (source-level, 2026-08-09) -- see "Fix applied" below. Full native-lane re-execution still not obtained (see caveat).

## Fix applied (2026-08-09)

Applied the exact fix candidate this doc already identified: added
`method == "set"` to the `is_dict_method_name` whitelist at
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:1232`, and
added a new dispatch arm (`receiver_is_dict and method == "set" and
args.len() == 2`) right after the `remove`/`delete` arm that lowers `.set(k,
v)` to the SAME `rt_dict_set` runtime call, with the same key-lowering
(`lower_dict_key`) and value-boxing (`box_runtime_value`) as `d[k]=v`'s
Index-assign lowering already uses (`mir_lowering_stmts.spl`, `Index(base,
index)` case). Returns the receiver handle, matching `.set()`'s documented
mutate-in-place/alias-return behavior (see
`reference_dict_bracket_assign_beats_set_both_engines` project memory).

Root cause confirmed: genuine bug, not working-as-intended. `"set"` was
simply absent from `is_dict_method_name`, the whitelist that routes Dict
method calls to their dedicated MIR lowering; `d[k]=v` never went through
that whitelist at all (different MIR construct -- Index-assign, not a method
call), so the two forms were never actually equivalent code paths despite
being intended as equivalent Dict-write APIs.

## Verification performed this pass

- `git diff origin/main -- src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`
  shows exactly the intended hunk (whitelist entry + new arm), clean against
  origin immediately before landing.
- `bin/simple lint src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`
  and a full `bin/simple test test/01_unit/compiler/dict_bracket_vs_set_spec.spl`
  run (which parses/typechecks the entire compiler source tree, including the
  edited file, as part of resolving its own imports) both completed with only
  pre-existing repo-wide warnings (`export use *`, deprecated generics syntax,
  cross-module symbol collisions) -- no syntax/type errors introduced by this
  change. The regression spec passed **3/3** (seed/interpreter lane).
- **Caveat, same as this doc's prior pass:** true end-to-end verification on
  the real self-hosted/native-codegen lane (the lane this defect actually
  affects) requires compiling the fixed compiler source into a fresh
  self-hosted binary, i.e. a bootstrap rebuild. That was explicitly out of
  scope for this task (no `bin/simple build bootstrap`), exactly as the prior
  pass on 2026-08-07 also deferred it. `bin/simple test`'s 3/3 pass exercises
  only the Rust bootstrap seed's interpreter/JIT, which -- per this doc's own
  prior finding -- was **never** the affected lane (the seed's own native Dict
  implementation is unrelated Rust code, untouched by this .spl-level fix).
  The fix is corroborated by direct source inspection (mirrors the
  already-working `d[k]=v` lowering call-for-call: same runtime symbol, same
  key/value lowering helpers, same argument count/order) rather than by a
  fresh native-lane execution trace.
- Regression surface: `get`, `contains_key`, `remove`/`delete`, `keys`,
  `values`, `has`/`contains` dispatch arms were not touched -- only a new arm
  was added and the whitelist gained one more name. The existing regression
  spec (`test/01_unit/compiler/dict_bracket_vs_set_spec.spl`) covers `d[k]=v`,
  `.set()`, `.get()`, `[]` read, and `.contains_key()` together; all pass.

## Status: OPEN -- narrower than the 2026-07-31 filing, and confirmed by a DIFFERENT symptom on the real native/self-hosted lane (superseded by "Fix applied" above)

## Correction to an earlier version of this doc

An earlier pass of this investigation ran its probes only through
`bin/simple` (the deployed `bin/release/x86_64-unknown-linux-gnu/simple`) and
declared the original defect "CLOSED (stale)" because both `.set()` and
`d[k]=v` round-tripped correctly there, under both `bin/simple run`
(Cranelift JIT, confirmed via `cranelift_jit::backend` log lines) and
`SIMPLE_EXECUTION_MODE=interpret bin/simple run`. **That binary is the Rust
bootstrap seed, not the self-hosted compiler** -- confirmed by:
`eprintln!("WARNING: this Rust-built Simple binary is a bootstrap seed
only...")` living in `src/compiler_rust/driver/src/seed_warning.rs` and firing
on every invocation; `tracing`-style ANSI/`ThreadId(...)` log formatting,
which is Rust `tracing`, not Simple's own logger; and 58 MB size consistent
with a statically-linked Rust binary carrying Cranelift.

The original 2026-07-31 filing (`builtin_dict_set_silent_insert_audit_2026-07-31.md`)
says explicitly: *"the interpreter tree-walk path and the Rust seed both
behave correctly ... only a native build/run exercises the broken paths."*
Measuring on the seed cannot discriminate "fixed" from "still broken on the
lane that was actually filed" -- it was never in the affected lane in the
first place. **The seed-lane results below stand as correct measurements of
the seed, not as a closure of the original defect.**

## What was actually available to test the real lane, and what it found

The only source-built (non-seed) Simple compiler present in the working tree
is `bootstrap/stage3/x86_64-unknown-linux-gnu/simple`. It has no `run` or
`test` subcommand (`error: unknown command 'run'`) -- only `compile
<file> --format=smf` and `native-build <file>.spl`, both of which lower
through the real self-hosted MIR pipeline (`src/compiler/50.mir/**`), the
actual lane the original filing and `doc/07_guide/language/dict_native_pitfalls.md`
are about.

Both `compile --format=smf` and `native-build` were tried on this binary, on
three probe files: bracket-only (`d["a"]=1`, no `.set()`), the full
bracket-vs-`.set()` probe, and a trivial `print("hello")` hello-world with no
Dict at all.

**All three probes segfault (exit 139) under this stage3 binary, including
the Dict-free hello-world.** This matches an already-tracked, unrelated
defect (`reference_stage3_helloworld_segv_is_borrow_checker_field_index_collision`
in project memory / `doc/08_tracking/bug/stage3_selfhost_nil_receiver_sigill_in_lower_expr_caller_2026-08-05.md`
and neighboring stage3 entries) -- **not filed again here**, and not
something this task attempted to fix (out of scope, and "no bootstrap
rebuild" per task constraints).

**But before crashing, only the probes that call `.set(` on a Dict print:**

```
[ERROR] MIR error: MIR lowering error: unresolved method call: set
```

The bracket-only probe and the hello-world probe never print this line --
they still segfault (from the unrelated pre-existing bug), but MIR lowering
does not choke on anything Dict/method-related first. This reproduces
identically under both `compile --format=smf` and `native-build`.

## Interpretation

On the real self-hosted/native-codegen lane available in this tree today,
**`.set()` on a builtin `Dict` fails MIR lowering outright** ("unresolved
method call") while `d[k]=v` lowers cleanly. This is not the same *symptom*
as the original 2026-07-31 filing (silent insert-drop, no error) -- it is
`unresolved method call: set`, a hard compile-time MIR error -- but it is the
same *conclusion*: `.set()` is broken on native codegen, `d[k]=v` is not.
Whether this is a regression from "silently drops" to "fails to lower" or
whether MIR lowering for `.set(` was already unwired at census time and the
prior report's evidence came from a different code path is not determined
here.

**A full read-back parity table (the kind produced against the seed below)
could not be obtained on this lane** because the pipeline cannot get past
`main()` for ANY program right now, Dict or not -- the unrelated segfault
blocks it before a native executable can be produced and run.

## Seed-lane results (Rust bootstrap seed, `bin/simple` / `bin/simple run`) -- NOT the affected lane, included for completeness only

Two probe files, run twice each on the seed: once with `bin/simple run`
(confirmed real Cranelift JIT engagement via `cranelift_jit::backend:
defining function ...` log lines under `SIMPLE_LOG=info`), once with
`SIMPLE_EXECUTION_MODE=interpret bin/simple run`.

| Read | seed JIT | seed interpret |
|---|---|---|
| `d["a"]` (bracket-written) | 1 | 1 |
| `d.get("a")` (bracket-written) | 1 | 1 |
| `d["b"]` (.set()-written) | 2 | 2 |
| `d.get("b")` (.set()-written) | 2 | 2 |
| `d.contains_key("a")` / `("b")` | true / true | true / true |
| `g_counts["hits"]` (.set(), cross-fn global) | 7 | 7 |
| `g_counts["misses"]` (bracket, cross-fn global) | 9 | 9 |
| `g_counts.keys().len()` | 2 | 2 |
| `g_headers["authorization"]` (.set(), text, cross-fn) | `Bearer xyz` | `Bearer xyz` |
| `g_headers["content-type"]` (bracket, text, cross-fn) | `json` | `json` |
| `g_headers.keys().len()` | 2 | 2 |

`bin/simple test test/01_unit/compiler/dict_bracket_vs_set_spec.spl`
(interpreter harness, local-dict cases only): `Results: 3 total, 3 passed, 0
failed`.

These rows are consistent with the original filing's own claim that the seed
was never broken -- they say nothing about whether the self-hosted lane is
fixed.

## `git diff origin/main` check (required by task constraints)

`src/compiler/50.mir/**` and `src/runtime/runtime_native.c` show as
untracked/"A" in `git status` relative to the current git index -- a
jj/git-colocation artifact per `.claude/rules/vcs.md`, not local edits this
session made. `git diff origin/main -- src/compiler/50.mir` does show a real
content hunk in `_MirLowering/function_lowering.spl` (unrelated to Dict --
removes 2 lines) already present on this working tree before this session
touched anything; not investigated further as it is out of scope and no
source file was edited to produce the findings above (measurement only).

## Root cause, confirmed against SOURCE (not just the stage3 artifact)

The stage3 binary was built today (11:28) by a concurrent session from a tree
with real content drift vs `origin/main`, and it cannot even native-build a
Dict-free hello-world -- on its own, `unresolved method call: set` from that
one binary is a weak signal (a half-broken build could produce that symptom
for reasons unrelated to source). Corroborated directly against source:

`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:1196`:

```
val is_dict_method_name = method == "keys" or method == "values" or method == "has" or method == "contains" or method == "contains_key" or method == "get" or method == "remove" or method == "delete"
```

This is the whitelist that makes the stage3 log's `[mir-method-call]
receiver-type method=contains_key` / `option-dispatch` / etc. dispatch lines
fire for `contains_key`, `get`, `keys`. **`"set"` is absent from this list.**
`d[k]=v` does not go through this method-dispatch path at all -- it lowers as
an Index-assign statement, a different MIR construct entirely, which is why
it never hits `is_dict_method_name` and never errors. So the stage3
`unresolved method call: set` is corroborated by source, not an artifact of
that one broken build: `.set()` on a builtin `Dict` is genuinely never wired
into this dispatch table.

A single line (`grep -rn '"set"' src/compiler/50.mir/_MirLoweringExpr/` found
no other Dict-write arm elsewhere in that directory) is the minimal,
well-scoped fix candidate: add `method == "set"` to `is_dict_method_name` and
give it an arm that lowers to the same instruction `d[k]=v`'s Index-assign
path already uses (two args: key, value; no return value read back). **Not
applied in this pass** -- this doc is measurement/root-cause only, per the
task's scope (verify first, fix only if safe and well-scoped; a MIR lowering
change was judged worth a deliberate follow-up commit + spec run rather than
folding into a measurement session already carrying two other findings).

## Follow-up recommendation

- Do not mark the original 2026-07-31 `.set()` census as closed. The 71
  remaining unconverted `.set()` sites in `dict_native_pitfalls.md` should
  stay flagged as risk -- if anything this finding (hard MIR-lowering
  failure, not silent drop) is a stronger reason to convert them, since a
  hard compile error means any of those 71 sites will simply fail to build
  the moment they're pulled into a native-build/self-hosted path, rather than
  quietly losing data.
- The fix: add `"set"` to `is_dict_method_name` at
  `method_calls_literals.spl:1196` and lower it like `d[k]=v`. Verify with a
  spec run plus a stage3 `native-build`/`compile` re-run of the two probe
  files above once the stage3 hello-world segfault (below) is separately
  fixed enough to test past `main()`.
- The unrelated stage3 hello-world segfault blocks ANY further native-build
  measurement on this tree until it's fixed; that is tracked separately and
  was not attempted here.

## Related

- `doc/08_tracking/bug/builtin_dict_set_silent_insert_audit_2026-07-31.md`
- `doc/07_guide/language/dict_native_pitfalls.md`
- `doc/08_tracking/bug/spec_harness_module_global_mutation_via_function_invisible_2026-08-07.md`
  (found while building the module-global probe as an `it`-block spec; a
  separate, non-Dict-specific `bin/simple test` harness limitation)
- Stage3 hello-world segfault (pre-existing, not filed here; see project
  memory `reference_stage3_helloworld_segv_is_borrow_checker_field_index_collision`)
- Spec: `test/01_unit/compiler/dict_bracket_vs_set_spec.spl` (interpreter-lane
  coverage only, via the seed's `bin/simple test`)
