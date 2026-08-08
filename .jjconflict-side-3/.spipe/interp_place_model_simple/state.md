# Lane PMS — pure-Simple interpreter place model

Status: **fix landed in source; verification redeploy-blocked** (2026-07-27, not committed)

## Question asked: do struct field reads alias or copy?

**They ALIAS.** Evidence, all in `src/compiler/10.frontend/core/interpreter/`:

- `value.spl:195` — `val_make_struct` stores `field_values: [i64]` (a vector of
  value_ids) into the `val_struct_values` arena. A struct value is a *handle*
  (arena index), and its fields hold handles.
- `value.spl:302` — `val_struct_get_field_idx(vid, idx)` returns
  `val_struct_values[vid][idx]` verbatim. No rebuild, no copy.
- `eval_access.spl:67-78` (and its duplicate `_EvalOps/access_literal_assign_eval.spl:148`)
  — `eval_field_access` returns exactly that handle.
- `value.spl:308` — `val_struct_set_field_idx` writes through the handle.
- `_EvalOps/call_method_eval.spl:639` — the method receiver is pushed as
  `arg_values[0]` and bound by `env_define` with **no copy**.

Therefore the assignment path AND the mutating-method-receiver path are already
depth-agnostic in the pure-Simple interpreter: `root.mid.inner.bump()` resolves
`root.mid.inner` to the real inner struct's handle and writes through it.

**The "2-level place model" is Rust-seed-only.** The loud error string
`"invalid assignment: deeply nested field access requires intermediate variables"`
exists at exactly one place in the tree:
`src/compiler_rust/compiler/src/interpreter/node_exec.rs:947`. Zero `.spl` hits.
That is lane PMR's file, not this lane's.

Reproduced (`build/pms_probe.spl`, both binaries run the *Rust* interpreter):

```
SIMPLE_EXECUTION_MODE=interpreter bin/simple run build/pms_probe.spl
  d1 PASS 1 | d2 FAIL got=0 | d2acc FAIL got=0 | d3 FAIL got=0 | selfroot FAIL got=0
bin/simple run build/pms_probe.spl          # JIT path
  all PASS
```

## What WAS defective in the pure-Simple interpreter (fixed here)

Two real place-model holes, both independent of the Rust bug:

1. **Compound assignment had no place path at all.**
   `eval_compound_assign_expr` accepted only `EXPR_IDENT` targets and errored
   `"invalid compound assignment target"` for `x.f += 1`, `self.n += 1`,
   `root.mid.inner.n += 1`, `arr[i] += 1`. Added `EXPR_FIELD_ACCESS` and
   `EXPR_INDEX` branches that evaluate the base **once** to a handle, read the
   old value through it, and write the result back through it — depth-agnostic
   by construction, and identical in shape to `eval_assign_expr`. Array
   elements are updated through the base handle exactly as the existing index
   *assignment* branch does, so array value semantics are unchanged.
   - `eval_access.spl` (`eval_compound_assign_expr`)
   - `_EvalOps/access_literal_assign_eval.spl` (byte-identical duplicate — both
     definitions land in the same flat symbol registry, so they must not diverge)

2. **Method bodies ran without their own LOAD_FAST frame.**
   `resolve_module_locals()` (`resolve.spl:391`) walks **every** `DECL_FN` in the
   arena — method bodies included — so a method's idents, starting with `self`,
   carry pre-resolved local slot indices. `eval_ident` (`eval.spl:345-358`) takes
   the fast path whenever `expr_i_val[eid] >= 0` **and** `env_has_frame()` — it
   does *not* check that the live frame belongs to this call.
   `eval_function_call` pushes a frame (`eval_calls.spl:326-350`); neither
   `eval_method_with_args` variant did. So a method invoked while a caller frame
   was live could resolve `self` to the **caller's** slot — the receiver place
   pointing at the wrong object, mutations lost or misdirected. Both variants now
   push/pop their own frame and own `eval_current_decl_id`:
   - `_EvalOps/call_method_eval.spl:656` (4-arg variant) — sets slots like
     `eval_function_call`, honouring `resolve_is_slot_shadowed`.
   - `eval_methods.spl:195` (legacy 2-arg variant) — pushes the frame with slots
     reset to `-1` and leaves them unset, because that binder does not bind params
     in slot order; `eval_ident` then correctly falls through to scope lookup.
   `env_push_frame` (`env.spl:212-224`) resets slots to `-1`, so where
   `local_count == 0` or slots go unset the behaviour is byte-identical to before.

Not changed (deliberately): array value semantics, `val_struct_deep_copy` value-type
param binding (`eval_calls.spl:342`), non-place receivers.

## NEW defect found while validating the probe (NOT this lane's, not fixed here)

`bin/simple run build/pms_probe.spl` — the **JIT/native** path, the one believed
correct at every depth — is green on all the plain-assignment and
mutating-method rows but RED on two compound-assignment rows:

```
cassign2 FAIL got=3  want=7     # c2.mid.inner.n += 4 ; c2.mid.inner.n += 3
cassign_idx FAIL got=10 want=12 # carr: [i64] = [1,2,3] ; carr[1] += 10
```

Signature: the *write* lands (the last one is observable) but the *read of the
old value* comes from a stale base — depth-2+ field places and **all** array
index places read `0` instead of the current element. Depth-1 field compound
assignment (`cassign1`) is fine. So: seed JIT/native lowers `place op= rhs` by
re-resolving the place for the store but not for the load. Distinct subsystem
from this lane (interpreter place model); recorded here rather than silently
normalised. The two probe rows are expected RED until it is fixed.

## Verification tier reached: **3 — correct-by-construction, redeploy-blocked**

- **Tier 1 (run the pure-Simple interpreter as a program) — ATTEMPTED, BLOCKED.**
  `build/pms_driver.spl` does work mechanically: it inlines `_core_run_pipeline`
  (module-private, unreachable through the flat registry) and drives
  `eval_init / ast_reset / must_use_scan_source / core_frontend_parse_reset /
  resolve_module_locals / eval_module` on a probe file. The host resolves every
  symbol and the inner interpreter runs. But the interpreter is entirely
  arena-globals based, and **cross-import module globals are a known-broken
  interpreter feature** — under the tower, integer literals and `==` misbehave
  (`build/pms_smoke.spl` showed a method returning literal `7` compare unequal to
  `7`, and a plain `q.n == 3` read fail). The tier produces false negatives on
  arithmetic, so it cannot certify anything. Do not re-derive this.
- **Tier 2 (targeted stage-2 native-build) — ATTEMPTED, no binary.**
  `SIMPLE_RUNTIME_PATH=src/compiler_rust/target/release bin/simple native-build
  --source src/compiler --source src/lib --source src/app --entry
  src/app/cli/bootstrap_main.spl -o build/pms_stage2/simple` exited after lint
  warnings without emitting a binary (`build/pms_stage2.log`). A full 3-stage
  bootstrap from another lane was saturating the machine at the time.
- **Parse/lint:** `bin/simple lint` parsed all four changed files with **zero**
  parse/syntax/E1xxx errors — so the edits are at least syntactically sound under
  the real front end. Its 30 findings are all `COLL006` "string concat in loop",
  reported against the header lines of pre-existing functions (`eval_dict_lit`,
  `eval_dict_comp`, `eval_method_call`, `eval_array_method`, and the
  `eval_set_error("... '" + name + "' ...")` builders inside
  `eval_method_with_args`' argument-remap loops). The added code contains no loop
  and no string concatenation, so none of them originate in it.

### Exact resume command for the next session

```bash
# 1. redeploy a binary embedding the pure-Simple interpreter
scripts/bootstrap/bootstrap-from-scratch.sh --deploy
#    (or, if a full-bootstrap seed already exists, the single-stage replay:
#     SIMPLE_BOOTSTRAP=1 src/compiler_rust/target/bootstrap/simple native-build \
#       --source src/compiler --source src/lib --source src/app \
#       --entry src/app/cli/bootstrap_main.spl \
#       -o build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple )

# 2. one-command check of this lane's property, depths 1/2/3 + compound assign
SIMPLE_EXECUTION_MODE=interpreter bin/simple run build/pms_probe.spl   # every line must read PASS

# 3. the oracle
bin/simple test test/01_unit/compiler/two_hop_field_method_mutation_spec.spl
```

Note for step 2/3: the oracle also needs lane PMR's Rust-seed fix
(`src/compiler_rust/compiler/src/interpreter/node_exec.rs:947`) as long as
`bin/simple` is the Rust seed — the two lanes gate each other.

## Artifacts

| Path | What |
|---|---|
| `build/pms_probe.spl` | depths 1/2/3 mutating-method + nested assign + compound assign + workaround-equivalence, PASS/FAIL per line |
| `build/pms_probe_min.spl` | same shape, no static ctors / no interpolation (tower-friendly) |
| `build/pms_driver.spl` | Tier-1 tower driver (blocked by cross-import globals; kept as the record) |
| `build/pms_smoke.spl` | tower sanity probe that exposed the tower's own arithmetic breakage |
| `build/pms_seed_interp.log`, `build/pms_np_interp.log` | the reproduction under both binaries |
| `build/pms_lint.log` | lint of the four changed files |
