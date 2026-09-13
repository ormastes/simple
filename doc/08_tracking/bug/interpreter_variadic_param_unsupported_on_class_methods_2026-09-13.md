# Variadic parameter works on a free function but is rejected on a class method

- Status: OPEN (2026-09-13)
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
