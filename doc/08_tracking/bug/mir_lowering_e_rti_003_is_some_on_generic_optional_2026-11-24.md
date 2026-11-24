# MIR lowering rejects `.is_some()` chained on a generic-optional call result (E-RTI-003)

Status: open (compiler). Call sites worked around 2026-11-24; no compiler fix
in this change. Source diagnosis is static; the failure itself was observed in
a real pure-Simple self-build (Phase 3 `native-build` of the release head).

## Observed

PR #11172 (`ef2a17bc62d`, merge `787a7205ec8`) rewrote
`src/lib/nogc_sync_mut/src/collections/adaptive_set.spl:102` from
`inner.remove(key) != nil` to `inner.remove(key).is_some()`. The build then
failed the module:

```
[go-to-end] failed stage=mir module=lib.nogc_sync_mut.src.collections.adaptive_set:
MIR lowering error: E-RTI-003: unsubstituted generic parameter in 'opt(p1)'
reached a concrete consumer at src/lib/nogc_sync_mut/src/collections/adaptive_set.spl:102:23
```

Two E-RTI-003 errors were counted for the module. The file holds exactly one
chained call on a call result (line 102; column 23 is the start of
`inner.remove(key)`), so the second error is most likely the same site
reported twice. That was not confirmed against the build log.

The `!= nil` form lowered. It is a binary operator, not a method call, so it
never asks RTI for the receiver's owner.

## Minimal repro shape

```simple
struct Store<K, V>:
    fn remove(key: K) -> V?:
        None

struct Facade<K>:
    inner: Store<K, bool>

    me remove(key: K) -> bool:
        var inner = self.inner
        inner.remove(key).is_some()      # E-RTI-003: 'opt(p1)'
```

The same shape with `self` as the inner receiver (`self.get(key).is_some()`
inside `impl Dict<K, V>`) reads the same way statically.

Note that `p1` is `V`, which is `bool` at the failing site. The parameter is
unsubstituted because the receiver's other argument (`K`) is the caller's own
type parameter, not because `V` is unknown.

## Cause (static reading)

`src/compiler/20.hir/return_type_interface_v1.spl`:

- `.is_some()` is a `MethodCall` whose receiver is itself a `MethodCall`.
  `receiver_owner_with_args` has no declared receiver type for it and the
  receiver is not a `Var`, so it falls to line 794:
  `require_concrete(resolve(callee_return(receiver, symbols, nil)))`.
- The nested `callee_return` resolves `inner.remove` through
  `static_or_value_owner` and `rti_concrete_owner_args_v1`. That helper
  returns `[]` when ANY owner argument has a `Param`
  (`rti_terms_have_param`). `Store<K, bool>` therefore loses both arguments
  and the row stays `opt(p1)`.
- `require_concrete` rejects it with E-RTI-003. The error leaves
  `callee_return` as an outer `Err`, and `rti_enum_match_subject_type`
  (`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:3058`)
  tolerates only E-RTI-001 there. Its E-RTI-003 fallback covers only the
  inner `require_concrete` arm. The outer arm calls `error_fatal`.

So any method chained on a call whose RTI row keeps a type parameter is
fatal, not only `.is_some()`/`.is_none()`. This is the boundary already
described in
`rti_chained_generic_factory_receiver_requires_concrete_owner_2026-11-23.md`;
this record is its first build-observed instance.

## Workaround applied

Do not chain a method on the generic call result.

| file | before | after |
|---|---|---|
| `src/lib/nogc_sync_mut/src/collections/adaptive_set.spl` `remove` | `inner.remove(key).is_some()` | `len()` before and after a discarded `inner.remove(key)` |
| `src/app/interpreter/collections/persistent_dict/dict.spl` `contains` | `self.get(key).is_some()` | `val found = self.get(key)` then `found.is_some()` |
| `src/app/interpreter/lazy/lazy_seq.spl` `any` | `self.find(predicate).is_some()` | local, then `.is_some()` |
| `src/app/interpreter/lazy/lazy_seq_fixed.spl` `any` | same | same |

`!= nil` was not restored for `adaptive_set`: `AdaptiveMap.remove` returns an
explicit `None` on a miss, and compiled `None == nil` is false, so every miss
would have reported a removal. The size delta does not depend on the optional's
representation: `remove` decrements `size` only on the present path.

The local-binding form is expected to lower because a `Var` receiver with no
declared nominal type ends in E-RTI-001, which the caller tolerates. That is a
static reading. None of the four edits was compiled or run: no full `simple`
binary was available and a compiler build was in progress.

## Not changed, same family

From the sweep of #11172, #11164, #11084-#11087, #11079, #11083, #11092 and
#11066 (1070 added `.is_some()`/`.is_none()` lines, 336 of them chained on a
call result):

- `X.unwrap().is_some()` on a `Result<T?, E>` local (11 lines, in
  `src/lib/common/task_runner/` and `src/os/apps/smux/`). Chained shape,
  concrete payload types, not confirmed to fail.
- `.is_some()` on a field of optional type inside files that declare generics
  (`simple_ring_async_v1.spl`, `daemon_sdk/local_gateway_v1.spl`). The receiver
  is a field access, a different RTI path.

## Compiler fix (not attempted)

Either substitute the concrete subset of owner arguments instead of dropping
all of them when one is a `Param`, or resolve builtin Option methods without
requiring a concrete nominal receiver. The 2026-11-23 record lists what a
repair must not do (treat every outer E-RTI-003 as a successful lookup).
