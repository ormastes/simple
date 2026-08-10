# Binding a class-typed FIELD to a local snapshots it — interpreter only

- **Status:** OPEN — engine divergence (interpreter vs JIT)
- **Filed:** 2026-08-10
- **Blocks:** `test/{02_integration,integration}/app/sj_daemon_mutual_exclusion_spec.spl`
  example *"sees the lease through SjClient -> fallback_exec -> handle_cli_args"*,
  deliberately left **RED**.

## What diverges

A `class` is a reference type, so passing one around must preserve identity.
It does — except when the value is obtained by **reading a field of an
aggregate and binding it**, and then mutated. Under the interpreter the root
does not observe the mutation; under the JIT it does.

`build/q18/probe_nesting.spl`, one file, both engines, with an absence control:

| probe | expression | interpreter | JIT |
|---|---|---|---|
| P1 | local class val, `c.bump()` | 1 | 1 |
| P2 | class in a **struct**, `s.c.bump()` | 1 | 1 |
| P3 | class in a **class**, `co.c.bump()` | 1 | 1 |
| P4 | two levels, struct-in-struct, `s2.inner.c.bump()` | 1 | 1 |
| P5 | two levels, class-in-class, `c2.inner.c.bump()` | 1 | 1 |
| **P6** | `val mid = c3.inner` … `mid.c.bump()`; read back `c3.inner.c.n` | **0** | **1** |
| — | NEGATIVE CONTROL: untouched instance | 0 | 0 |

Every in-place chained form agrees. Only the **bind-then-mutate** form (P6)
splits, and the negative control is 0 in both engines, so no engine is
trivially answering "1".

Note this is the mirror image of the usual advice: the documented workaround
for erased-receiver chains is "introduce an intermediate typed `val`". For a
class-typed field that workaround is precisely what breaks identity under the
interpreter.

## Production consequence — the RED example

`src/app/sj/client.spl:38` is exactly the P6 shape:

```
fn exec_args(client: SjClient, argv: [text]) -> SjResult:
    _wrap(fallback_exec(client.handler, parsed.argv, rt_getpid()))
```

`client.handler` is read out of the `SjClient` struct and handed on. Under the
interpreter each such read yields a handler whose `LeaseManager` is a fresh,
empty instance, so no request through `SjClient` can observe a lease taken by
another. Measured after `LeaseManager` was made a class
(`build/q18/probe_client.spl`, interpreter):

```
D1.acquired=true count=1                       # handler held in a local val — OK
D2.acquired=true count_chained=0               # via client.handler.lease_manager — LOST
D3.acquired=true count_via_val=1  back_through_client=0
D4.fallback_exit=0                             # fallback_exec(c2.handler, …)  -> no exclusion
D5.fallback_via_val_exit=75                    # fallback_exec(h2, …)          -> exclusion works
```

D5 vs D4 is the whole bug in two lines: identical call, one through a bound
field, one through a local.

**This is NOT fixed by making the containers classes.** Converting
`SjRequestHandler` and then `SjClient` from `struct` to `class` was tried and
changed nothing (D2 stayed 0 in both cases); those edits were reverted rather
than shipped as no-op churn. The defect is in how the interpreter materialises
a class-typed field read, not in the container's kind.

## Why the spec is left RED, not softened

Per repo rule, a correctly-failing spec pinning a real defect is not weakened,
marked pending, or deleted. The three examples that do not depend on this
defect (direct-handler exclusion, its negative control, lease release) are
GREEN and guard the fix that did land.

## Unblock condition

Interpreter materialises a class-typed field read as the same instance the
aggregate holds. Then P6 reads 1 in both engines and the RED example goes
green with no change to its assertions.
