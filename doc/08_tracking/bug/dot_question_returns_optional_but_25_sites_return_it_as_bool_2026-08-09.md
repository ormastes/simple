# `.?` yields `T?`, but 25 `-> bool` functions return it directly

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 01).

**Filed:** 2026-08-09 (stream F3)
**Found via:** `feature/usage/wasm_compile` — row 27 of
`gated_specs_are_tautology_shells_2026-08-09.md` (P15, `1bc53420716`)
**Fixed here:** 1 of 25 sites (`wasm_backend.spl`). The other 24 are UNFIXED.

## The defect

`.?` (`EXPR_EXISTS_CHECK`) is **not** a boolean predicate. It is a
value-or-nil operator. Both the AST definition and the interpreter say so:

```
src/compiler/10.frontend/core/_AstExpr/nodes.spl:63
const EXPR_EXISTS_CHECK = 49  # .? existence check (returns T? — value if present, nil if absent)
```

```
src/compiler/10.frontend/core/interpreter/eval.spl:436-444
if tag == EXPR_EXISTS_CHECK:
    ...
    val normalized_vid = eval_option_binding_value(base_vid)
    if val_exists(normalized_vid):
        return normalized_vid          # <-- the PAYLOAD, not `true`
    else:
        return val_make_nil()          # <-- nil, not `false`
```

Nevertheless **every** tail-position use of `.?` in the repo sits in a
function declared `-> bool` and returns it unconverted. A census of
`^\s*<expr>\.\?\s*$` in tail position finds **25 sites, and 25 of 25 declare
`-> bool`**. Each leaks `nil` or the raw payload to its callers.

The `-> bool` return type is **not enforced** — the type checker accepts a
`text?` body in a `-> bool` function without a diagnostic. That is a second,
separable defect and is why this survived so long.

## Why it stayed invisible

Callers almost always use these predicates in truthy position (`if
x.has_errors():`), where payload-vs-`true` and `nil`-vs-`false` behave
identically. It only breaks on **strict** comparison. `expect(...).to_equal(true)`
is strict; `== true` is not — a `== true` probe on the same broken code returns
`true` for a text payload, so an over-casual repro will report the bug as fixed
when it is not. Use `to_equal`, not `==`, when confirming this family.

## Reproduction (before the fix)

```bash
SIMPLE_MODULE_LIMIT=4000 SIMPLE_TIMEOUT_SECONDS=3600 SIMPLE_WASM_TEST=1 \
  bin/simple test test/03_system/feature/usage/wasm_compile_spec.spl
```

```
expected nil to equal false            # js_glue absent  -> leaked nil
expected const x = 1; to equal true    # js_glue present -> leaked the payload
SPEC FILE VERDICT: ... declared>=36 executed=36 passed=34 failed=2 dropped=0
```

After the one-line fix in `wasm_backend.spl`: `passed=36 failed=0`.
Sabotage check (`!= nil` -> `== nil`) flips both cases
(`expected true to equal false`, `expected false to equal true`), so the spec
genuinely covers both directions.

## The 25 sites

Fixed:

| file:line | function |
|---|---|
| `src/compiler/70.backend/backend/wasm_backend.spl:692` | `has_js_glue()` — **FIXED (F3)** |

Unfixed — same defect, one per line:

| file:line | function | body |
|---|---|---|
| `src/app/interpreter/collections/persistent_dict/dict.spl:75` | `contains()` | `self.get(key).?` |
| `src/app/interpreter/core/symbol.spl:120` | `contains()` | `self.map[s].?` |
| `src/app/interpreter/lazy/lazy_seq.spl:415` | `any()` | `self.find(predicate).?` |
| `src/app/interpreter/lazy/lazy_seq_fixed.spl:413` | `any()` | `self.find(predicate).?` |
| `src/app/package.registry/auth.spl:44` | `save_credentials()` | `write_result.ok.?` |
| `src/app/pkg/lock.spl:47` | `has_entry()` | `self.find_entry(name).?` |
| `src/compiler/00.common/effects_cache.spl:55` | `has_violations()` | `self.violations.?` |
| `src/compiler/20.hir/inference/infer.spl:215` | `has_errors()` | `self.errors.?` |
| `src/compiler/25.traits/associated_types.spl:42` | `is_resolved()` | `self.resolved.?` |
| `src/compiler/25.traits/trait_def.spl:58` | `has_default()` | `self.default.?` |
| `src/compiler/30.types/type_system/checker.spl:277` | `has_errors()` | `self.errors.?` |
| `src/compiler/35.semantics/verification_checker.spl:143` | `has_violations()` | `self.violations.?` |
| `src/compiler/40.mono/monomorphize/binding_specializer.spl:40` | `has_bindings()` | `self.bindings.?` |
| `src/compiler/70.backend/backend/llvm_backend.spl:344` | `has_object_code()` | `self.object_code.?` |
| `src/compiler/70.backend/linker/macho_inspect.spl:204` | `macho_has_uuid()` | `lc.?` |
| `src/compiler/70.backend/linker/pe_parser.spl:299` | `pe_has_codeview()` | `obj.codeview.?` |
| `src/compiler/99.loader/jit_instantiator.spl:200` | `can_jit_instantiate()` | `self.find_possible(symbol).?` |
| `src/compiler_rust/lib/std/src/verification/lean/runner.spl:102` | `is_environment_error()` | `self.environment_error.?` |
| `src/lib/gc_async_mut/cli/simple_parser_api.spl:61` | `has_subcommand()` | `self.subcommand.?` |
| `src/lib/nogc_async_mut/actor/mailbox.spl:47` | `expects_reply()` | `self.reply_id.?` |
| `src/lib/nogc_async_mut/cli/simple_parser_api.spl:61` | `has_subcommand()` | `self.subcommand.?` |
| `src/lib/nogc_sync_mut/cli/simple_parser_api.spl:64` | `has_subcommand()` | `self.subcommand.?` |
| `src/lib/nogc_sync_mut/conf.spl:70` | `conf_has()` | `c.entries.get(key).?` |
| `src/lib/nogc_sync_mut/database/server/durability.spl:353` | `durable_file_loads()` | `SdnDatabase.load(path).?` |
| `src/os/services/vfs/vfs.spl:142` | `in_container()` | `self.container_view.?` |

Note the ones over **lists**, not options — `self.errors.?`,
`self.violations.?`, `self.bindings.?`. There `.?` returns the list itself or
nil, so `has_errors()` hands callers a list. Whether `.?` is even meant to
apply to a list is a separate open question.

## Why only one was fixed here

F3's assigned scope was the single `wasm_compile` row. `llvm_backend.spl:344`
is owned by stream F2 (LLVM backend) and was deliberately left alone —
**that is a cross-stream overlap, not an oversight.** The remaining 23 sit in
`20.hir`, `25.traits`, `30.types`, `35.semantics`, `40.mono`, `99.loader`,
`src/lib/**` and `src/os/**`; each needs its own caller audit, because a
predicate that has always returned a truthy payload may have callers depending
on the payload. A blind sweep of all 24 is exactly the kind of speculative
bulk edit that should not ride along with a one-row fix.

## Open questions

1. **Which side is wrong — the operator or the 25 call sites?** 25 of 25 uses
   treat `.?` as a predicate. Either the language intends a predicate and
   `nodes.spl:63` + `eval.spl:436` are the defect (in which case one compiler
   fix repairs all 25), or the operator is right and 25 sites are wrong. This
   needs a language-owner ruling before the sweep. **Do not sweep first.**
2. **Why is `-> bool` not enforced?** A `text?` body in a `-> bool` function
   draws no diagnostic. Fixing that turns this whole family into compile
   errors, which is the durable fix regardless of how (1) is decided.
3. Only the interpreter path was measured. The native/JIT lowering of
   `EXPR_EXISTS_CHECK` (`convert_nodes.spl:1002`,
   `compile_c_entry.spl:221`) was **not** checked and may diverge again.

## STILL_PRESENT — re-verified 2026-08-17 (P2 triage, compiler lane)

Re-measured at HEAD 2026-08-17: the site count has GROWN, not shrunk. A census
over all `src/**/*.spl` for a tail-position `.?` inside a function whose
signature contains `-> bool` finds **29 sites** (doc recorded 24 remaining);
about 22 are a bare `X.?` tail, the rest are `a.? and b.?` style compounds.
Representative live sites:

- `src/lib/nogc_sync_mut/ffi/llvm_loader.spl:41` — `return _llvm_lib.?`
- `src/compiler/70.backend/backend/llvm_backend.spl:344` — `self.object_code.?`
- `src/compiler/25.traits/trait_def.spl:58` — `self.default.?`
- `src/app/pkg/lock.spl:47` — `self.find_entry(name).?`
- `src/compiler_rust/lib/std/src/core/regex_api.spl:458` — `return search(...).?`

`wasm_backend.spl` no longer appears, i.e. exactly one site was fixed. This is a
shared root cause with
`dot_question_truthy_op_returns_payload_as_call_arg_2026-07-20.md` -- both are
the same `EXPR_EXISTS_CHECK` payload leak at
`src/compiler/10.frontend/core/interpreter/eval.spl:443-450`, seen in return
position and in argument position respectively. Fixing that one site retires
both docs; patching the 29 call sites individually does not.

NOT FIXED by this lane (interpreter path owned by a concurrent P1 lane).
