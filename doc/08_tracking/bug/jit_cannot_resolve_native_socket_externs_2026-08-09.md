# JIT cannot resolve the native socket externs — every "JIT mode" networking run is silently an interpreter run

- **Filed:** 2026-08-09
- **Status:** OPEN
- **Severity:** Medium (correctness of engine claims; performance cliff)
- **Component:** Cranelift JIT external-symbol registration / `src/runtime` socket FFI
- **Binary measured:** `bin/release/x86_64-unknown-linux-gnu/simple`
  (`readlink -f bin/simple`)

## Summary

`native_tcp_bind`, `native_tcp_close`, `native_udp_bind` and `native_udp_close`
are not registered with the Cranelift JIT module. Any program that declares one
of them fails JIT compilation with an unresolved-external-symbol error and the
**whole module** is dropped back to the tree-walking interpreter. So
`SIMPLE_EXECUTION_MODE=jit` on networking code does not select the JIT at all —
it selects the interpreter with an extra compile attempt in front of it.

This was found while retrofitting `test/03_system/feature/usage/networking_spec.spl`
onto a real out-of-process engine probe
(`scripts/check/check-engine-claiming-specs-use-probe.shs` debt retirement).
That spec has a describe block literally titled **"JIT Compilation Mode"** with
examples named *"tcp bind compiles in JIT mode"* and *"udp bind compiles in JIT
mode"*. The title is false: tcp bind does not compile in JIT mode.

## Reproduction

```
$ cat /tmp/net.spl
extern fn native_tcp_bind(addr: text) -> (i64, i64)
fn main() -> void:
    val (h, e) = native_tcp_bind("127.0.0.1:0")
    print("TCP ok=" + (h > 0).to_text())

$ SIMPLE_EXECUTION_MODE=jit bin/simple run /tmp/net.spl
[jit-fallback] unresolved external symbol 'native_tcp_bind': whole module
dropped to the interpreter (expect ~100-1000x slowdown). Set SIMPLE_JIT_STRICT=1
to turn this into a hard error.
[INFO] JIT compilation failed, falling back to interpreter: Cranelift JIT
compile: Module error: unresolved external symbol 'native_tcp_bind' would
NULL-jump in JIT; deferring to interpreter
TCP ok=true
```

Strict mode confirms it is a real resolution failure, not a heuristic demotion:

```
$ SIMPLE_JIT_STRICT=1 SIMPLE_EXECUTION_MODE=jit bin/simple run /tmp/net.spl
error: Cranelift JIT compile: Module error: SIMPLE_JIT_STRICT: unresolved
external symbol 'native_tcp_bind' would NULL-jump in JIT; refusing to fall back
to the interpreter
```

`native_udp_bind` reproduces identically in a file of its own, so this is not
one bad symbol contaminating a module — each socket extern is independently
unresolved.

## Why it matters

1. **Every engine claim about networking is unfalsifiable today.** A probe run
   under `"jit"` and one run under `"interpret"` execute the same interpreter,
   so an A/B looks like agreement no matter what the JIT would have done. Any
   future JIT-only networking defect is invisible.
2. **Silent 100-1000x performance cliff** for any server-shaped program: one
   socket extern demotes the entire module, including all the hot code that had
   nothing to do with sockets (this is the documented
   whole-module-demotion behaviour, see
   `.claude/rules/testing.md` — "One unsupported operation silently demotes the
   WHOLE program to the interpreter").
3. The fallback notice goes to **stderr**, so a caller scoring stdout — the
   documented and correct way to score a probe — cannot see it.

## Current pin

`test/03_system/feature/usage/networking_jit_probe.spl` binds real TCP/UDP
sockets on port 0 and self-scores, and
`test/03_system/feature/usage/networking_spec.spl` asserts BOTH the probe's
`PROBE VERDICT: PASS` and the presence of the `[jit-fallback] unresolved
external symbol 'native_tcp_bind'` line on stderr under `"jit"`. That fallback
assertion is a pin on measured reality, **not approval**: when the externs are
registered with the JIT it will go RED and must then be replaced by an
assertion of a genuinely compiled run.

## Unblock condition

Register the socket externs in the JIT's symbol table alongside the other
`rt_*` / `native_*` runtime entry points, then flip the spec's fallback
assertion to a real compiled-lane assertion and re-run both engines.
