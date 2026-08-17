# cranelift `__simple_ssa_phi` N-ary-join guard now fires in a real spec

- **Filed:** 2026-08-17
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Severity:** medium (one RED example; guard prevents a silent miscompile)
- **Component:** `src/compiler/70.backend/backend/cranelift_codegen_adapter.spl`
- **Related:** `src/compiler/70.backend/backend/llvm_lib_translate_expr.spl:714`
  carries the same restriction for the llvm-lib backend.

## Symptom

`test/feature/plugin/sugar_plugin_spec.spl` — 12 passed, 1 failed:

```
Error: eprint(ranelift] ERROR: __simple_ssa_phi has {args.len()} args
(N-ary join) with no stack slot; this fallback only supports a single
then/else pair")
```

(The mangled `eprint(ranelift]` prefix is the runner echoing the guard's own
`eprint` source text; the guard is `cranelift_codegen_adapter.spl:728-730`.)

Sweep evidence: `test/feature/plugin` directory run, 31 total / 30 passed /
1 failed; the other three plugin specs (`custom_block_plugin_spec`,
`plugin_startup_block_spec`, `runtime_api_plugin_spec`) are all fully green,
so the failure is specific to sugar-plugin lowering.

## Why this is a real defect, not just a loud guard

The guard's own comment (lines 717-724) states the assumption that has now
been falsified:

> No caller currently emits N-ary joins through this backend, so this is
> latent; guard it loudly rather than miscompiling silently if that ever
> changes.

That "ever changes" has happened. The sugar-plugin lane emits an
`__simple_ssa_phi` with more than one incoming pair (an elif-ladder join)
for a destination that has no stack slot registered in `slot_map`.

The two fallback arms are structurally incapable of handling it — they read
only `args[1]` (`args.len() >= 4`) or `args[0]` (`args.len() > 0`) and have
no predecessor-block information with which to choose the correct incoming
value. So the guard is correct to refuse; the fix is to make the N-ary case
representable, not to widen the fallback's guesswork.

## Secondary concern in the guard itself

On the guard path the handler does a bare `return` (line 730) after the
`eprint`. That leaves `value_map[dest_id]` **unset** for the phi's
destination. Any later instruction translating that local will therefore
miss, so the loud failure mode is followed by an undefined-value read rather
than a clean abort. Whatever the eventual fix, the guard path should trap
(`cranelift_trap`) the way the `unsupported intrinsic` arm at line 746-748
does, rather than fall out of the handler leaving a hole in `value_map`.

## Fix direction (not attempted here)

Either

1. ensure every `__simple_ssa_phi` destination gets a `slot_map` entry — the
   stack-slot path at line 737-741 is already arity-agnostic and handles
   N-ary joins correctly today, so guaranteeing slot allocation for phi
   destinations makes the fallbacks unreachable; or
2. give the fallback real phi semantics by threading the predecessor block
   through, which is the larger change.

(1) is the smaller and likelier-correct fix, but it was not attempted in this
sweep because it needs verification that slot allocation for phi destinations
does not regress the stage4 lane's `LocalId?`-argument workarounds referenced
throughout this file.

## Repro

```
SIMPLE_TIMEOUT_SECONDS=600 bin/simple test test/feature/plugin/sugar_plugin_spec.spl
```

---

## CLOSED 2026-08-17 — misdiagnosis; the real red was a stale spec assertion

Re-verified against `test/feature/plugin/sugar_plugin_spec.spl` on the current
tree. The N-ary-join guard **does not fire**. The failing example was

```
✗ FR-PLUG-0004 blocker: Cranelift matrix ops still use generic fallback
```

a source-contract example (`sugar_plugin_spec.spl:236-242`) that asserted the
*blocker still existed*. Its four `to_contain` strings included
`"# Pow, MatMul, Broadcast ops: fall back to integer add"` and the old
`fn translate_binop(...)` signature — both now absent (measured: 0 occurrences
each). The `__simple_ssa_phi` / `eprint("[cranelift] ERROR: ...")` lines quoted
in this doc's Symptom section are the runner echoing the *asserted source text*
in its failure diff, exactly the hazard `.claude/rules/testing.md` § F3 warns
about; they are not runtime output. The mangled `eprint(ranelift]` prefix was
the clue and was misread as evidence of execution.

The blocker itself is genuinely fixed in
`src/compiler/70.backend/backend/cranelift_codegen_adapter.spl:1107-1121`:
`MatMul` and all five `Broadcast*` ops dispatch through
`translate_runtime_import_call_i64` to `__simple_runtime_matmul` /
`__simple_runtime_broadcast_{add,sub,mul,div,pow}`. Only `Pow` and future
unsupported ops remain on the `cranelift_iadd` fallback.

The example was repointed at the current contract rather than deleted, so it
still fails if any matrix op regresses back onto the generic fallback.

### Evidence

Before (stale assertion):
```
SPEC FILE VERDICT: test/feature/plugin/sugar_plugin_spec.spl declared>=13 executed=13 passed=12 failed=1 dropped=0
Results: 13 total, 12 passed, 1 failed
```
After:
```
SPEC FILE VERDICT: test/feature/plugin/sugar_plugin_spec.spl declared>=13 executed=13 passed=13 failed=0 dropped=0
Results: 13 total, 13 passed, 0 failed
```

No product code changed, so no reproducing/generalization spec pair is shipped:
the corrected example in `sugar_plugin_spec.spl` **is** the regression guard,
and there is no defect to reproduce. The `__simple_ssa_phi` N-ary-join
restriction at `cranelift_codegen_adapter.spl:728-730` and its llvm-lib twin
remain in place as designed and unexercised by this spec.

## 2026-08-17 content triage (w0001 ZCLAIMED, source-inspection only)

Verdict: STILL-OPEN (source comment is stale relative to the report)

The guard is present at `src/compiler/70.backend/backend/cranelift_codegen_adapter.spl:~728`,
but its comment still asserts the case is unreachable:

```
# first pair. No caller currently emits N-ary joins through
# this backend, so this is latent; guard it loudly rather
# than miscompiling silently if that ever changes.
```

The bug report says the guard DOES fire in sugar_plugin_spec, so either the
comment or the report is wrong. Owner path: src/compiler/70.backend/**.
