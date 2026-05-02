# Bug Report: log facade backend-swap path broken under interpreter

**Bug ID:** B-LOG-BACKEND-INTERP
**Date:** 2026-04-25
**Severity:** P2 - Medium (blocks AC-6b verification under interpreter; the
underlying compiler limitation is the load-bearing fix)
**Component:** `src/lib/log.spl` (callers) + Simple compiler semantic analysis
**Status:** Open, surfaced by sstack/log-lib-drivers Phase 7

## Summary

`ring_backend_new(...)` and `log_register_backend(...)` in
`src/lib/log.spl` use the patterns

```simple
rb.ops.self_ptr = _g_ring_registry.len()    # ring_backend_new, line 252
_g_backends[i].active   = true              # log_register_backend, line 202
_g_backends[i].self_ptr = ops.self_ptr      # log_register_backend, line 203
```

Both forms — `obj.field1.field2 = …` and `arr[i].field = …` — are
rejected by the interpreter's semantic pass with:

```
error: semantic: invalid assignment: field assignment requires
identifier or simple nested field access as object
```

This means **every code path that registers a backend or constructs a
RingBackend fails at load time under interpreter mode**. The
log_facade_backend_swap spec (AC-6b) has therefore never genuinely
executed — it is a textbook case of the false-green pattern documented
in `feedback_compile_mode_false_greens.md`.

## Reproduction

```bash
cd /home/ormastes/dev/pub/simple-phase5b
cat > /tmp/repro.spl <<'EOF'
class Slot:
    active: bool

val arr: [Slot] = [Slot(active: false)]
arr[0].active = true
print("got " + arr[0].active.to_text())
EOF
bin/simple /tmp/repro.spl
# error: semantic: invalid assignment: field assignment requires
# identifier or simple nested field access as object
```

```bash
cat > /tmp/repro2.spl <<'EOF'
class Inner:
    n: i64
class Outer:
    inner: Inner
val o = Outer(inner: Inner(n: 0))
val list = [o]
list[0].inner.n = 5    # also fails
print(list[0].inner.n.to_text())
EOF
bin/simple /tmp/repro2.spl
```

The simpler form `o.inner.n = 5` (no array index) DOES work, so the
limitation is specifically about combining array-index access with
field assignment.

## Acceptance Criteria Impact

`AC-6b` of `sstack/log-lib-drivers` ("backend swap at runtime") — the
spec's executable assertions (`expect(ring_backend_count(sink_a)).to_equal(3)`)
cannot run because `ring_backend_new()` itself fails to load. Marked
PARTIAL (`[~]`) in the Phase 7 final AC table; the level-filter half
of AC-3 + AC-6a is verified by the executable proof at
`test/integration/log_facade_runtime_check.spl`.

## Plan

1. **Compiler fix** (load-bearing): teach the semantic analyser to accept
   `LValue ::= Path '.' Ident | Path '[' Expr ']'` recursively for
   assignment targets. The MIR/codegen side already supports it (the
   self-hosted `bin/simple` and the Cranelift backend pass when given
   the same AST). The restriction lives in the semantic check that
   classifies assignment targets.
2. **Workaround** (until #1 lands): rewrite the register/swap fast path
   to avoid `arr[i].field = …`. Two options:
   - Use a parallel array of `i64`s (`_g_backend_active[i] = 1`) instead
     of a struct array; field-on-int assignment doesn't trigger the
     check.
   - Replace the assignment with a re-build: `_g_backends[i] =
     _BackendSlot(active: true, self_ptr: …, kind: …)`.
3. Re-run `test/integration/log_facade_runtime_check.spl` with backend-
   swap assertions added once #1 or #2 lands.

## Links

- Architecture spec: `.sstack/log-lib-drivers/state.md` §3-arch §B
  (slot table) + §H (atomic swap).
- Phase 4 spec (currently false-greening on this):
  `test/unit/lib/log_facade_backend_swap_spec.spl`.
- Phase 7 verify report: `.sstack/log-lib-drivers/state.md` §7-verify.
