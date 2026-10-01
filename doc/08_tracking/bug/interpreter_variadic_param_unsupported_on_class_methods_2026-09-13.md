# Variadic parameter works on a free function but is rejected on a class method
## Closed 2026-09-16 — Status RESOLVED 2026-09-13: fixed by PERF-9, oracle spec RED 1/9 to GREEN 9/9

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

- Status: RESOLVED (2026-09-13) — diagnosed and pinned as an oracle by PERF-7;
  fixed by PERF-9 in `bind_args_with_values_named`, with a nine-oracle spec at
  `test/01_unit/interpreter/variadic_method_params_spec.spl` (RED 1/9 on the
  pre-fix seed, GREEN 9/9 after).
- Found by: PERF-7 (interpreter per-call cost), while recording parity oracles
  for the owned-receiver method-call kernel.
- Binary: private seed `simple.base`, sha256 `6903816380d27188...`, built from
  `origin/main` d522cc98da2 with `cargo build --release --bin simple`.

## Repro

Free function — works:

```simple
fn addall(nums...) -> i64:
    var t = 0
    for n in nums:
        t = t + n
    t
fn main():
    print("RESULT elapsed_us=1 acc={addall(1, 2, 3)} iters=1")
```

```
$ SIMPLE_EXECUTION_MODE=interpreter simple.base run vararg_free.spl
RESULT elapsed_us=1 acc=6 iters=1
```

The same variadic as a class method — rejected:

```simple
class Sum:
    total: i64
    me addall(self, nums...):
        for n in nums:
            self.total = self.total + n
    fn value(self) -> i64:
        self.total
fn main():
    var s = Sum(total: 0)
    s.addall(1, 2, 3)
    print("RESULT elapsed_us=1 acc={s.value()} iters=1")
```

```
$ SIMPLE_EXECUTION_MODE=interpreter simple.base run vararg_method.spl
error: semantic: function expects 1 argument(s), but 3 were provided
$ echo $?
1
```

(`test/05_perf/interp/fixtures/owned_call/sem_varargs.spl` is this fixture.)

## Where

The owned-receiver method kernel binds arguments through
`bind_args_with_values_named`
(`src/compiler_rust/compiler/src/interpreter_call/core/arg_binding.rs:551`),
which builds `params_to_bind` by filtering out `self` and then rejects
`args.len() > params_to_bind.len()` outright. It has no variadic case at all —
the collect-the-rest handling lives only in the plain `bind_args` path that free
functions take. `self` is correctly excluded (the count in the message, 1, is the
`nums` parameter alone), so this is not a self-counting bug: the binder simply
does not implement variadics.

## Why it is filed rather than fixed

Out of PERF-7's scope (per-call COST, not call semantics), and the fix is a
behaviour change that needs its own parity spec: a variadic parameter must
collect the remaining positional arguments into an array while still honouring
labelled arguments and defaults for the parameters before it, and the
empty-variadic case (`s.addall()`) must bind an empty array rather than fall
into the default/missing-argument path.

## Pinned meanwhile

`test/05_perf/interp/owned_method_call_parity_spec.spl` records the CURRENT
rejection as an oracle (rc 1, `expects 1 argument`), explicitly marked as
recorded base behaviour and not an endorsement, so that the per-call cost work
neither silently repairs nor silently worsens it. When this bug is fixed, that
scenario must be rewritten to assert the working value (`6`), not deleted.

## Fix (PERF-9, 2026-09-13)

`bind_args_with_values_named` — the pre-evaluated binder every method dispatch
goes through — rejected any call with more arguments than declared parameters
before it looked at what those parameters were, so the `variadic` flag
`Parameter` has always carried was unreachable from a method. Now:

- the fixed-arity ceiling applies only when no bindable parameter is variadic;
- a positional argument at or past the variadic slot joins the tail, so a
  one-argument call binds a one-element tuple rather than the bare value (the
  shape `for n in nums` needs);
- a LABEL naming the variadic parameter contributes one element rather than
  binding the whole slot;
- the parameter binds to `Value::Tuple(tail)` — the exact representation the
  expression binder `bind_args` produces — empty when nothing was supplied, and
  deliberately not coerced or unit-validated because `param.ty` describes an
  ELEMENT;
- PERF-7's wholly-positional fast path is skipped when a variadic parameter is
  present: its identity (argument `i` fills parameter `i`) does not hold for a
  slot that binds a tuple of the tail.

The owned-receiver container write-back needed the same guard: it zips
parameters against argument expressions and writes any container-valued
parameter back into the variable the argument named, so an unguarded loop would
have replaced the caller's first tail variable with the tuple. It now stops at
the variadic parameter positionally and skips it when labelled — the same stop
`bind_args`' own write-back already took. Two of the nine oracles are exactly
that: the caller's variables must be unchanged after a variadic method call.

