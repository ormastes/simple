# Unguarded `T?` passed to a `T` parameter is accepted by default (2026-11-14)

**Status:** open. This is a pre-existing hole. It was found while reviewing
`optional_struct_payload_narrowing_native_2026_11_13`, and that fix neither
widens nor narrows it.
**Severity:** P2. Ill-typed programs compile, and a None argument causes a wild
read instead of a diagnostic.

## Reproduction

```simple
struct E:
    a: i64

fn enc(x: E) -> i64:
    x.a

fn f(v: E?) -> i64:
    enc(v)          # no nil guard, no `!`, no `if val`

fn main():
    val s: E? = Some(E(a: 7))
    print("some=" + f(s).to_text())
    print("none=" + f(None).to_text())
```

Rust seed `run` at
`/home/yoon/dev/simple-dynlib-20261113/build/cargo-target/release/simple`,
worktree base c8535664423:

```
some=103079215111      # silent wrong value: the Option box header, not 7
timeout: the monitored command dumped core   # f(None)
```

## Where it is accepted

- **Pure-Simple HM checker.** `HmInferContext.unify`
  (`src/compiler/30.types/type_infer/core.spl`) has no `Optional <-> Named`
  rule, so the call is a unification error. Narrowing (`lookup_with_narrowing`)
  only applies after a guard. The diagnostic is not enforced, though:
  `typecheck_pass_severity_for_name`
  (`src/compiler/80.driver/driver_typecheck_severity.spl`) resolves the
  default/moderate/strict profiles to `Advisory`, which is log-only. Only
  `robust` warns, and only `critical`/`verified` deny.
- **Rust seed.** No diagnostic at all ("seed aggregate typing not
  authoritative"). It runs and returns the box header for Some, and SIGSEGVs
  for None.

## Effect of the 2026-11-13 MIR fix

`option_record_argument_payload_v1` unwraps a `T?` argument for a declared `T`
parameter with `rt_unwrap_or_self`. With that fix, the pure-Simple native lane
behaves as follows:
- Some -> passes the record (previously it passed the box: wrong value or
  crash);
- None -> `rt_unwrap_or_self` returns the None word itself, so the callee
  wild-reads exactly as before.

The set of accepted programs is unchanged, and no new nil is accepted.

## Fix direction

1. Make the HM `Optional(T)` vs `T` argument mismatch a hard error (Deny) at
   every profile once narrowing covers `if v == nil: return`, match binders, and
   `elif`. Census the corpus first, the same way the Advisory ladder migration
   did.
2. Until then, the MIR argument unwrap could emit a checked unwrap
   (`rt_option_is_none` then panic, as the text receiver path does) so that a
   None argument traps deterministically instead of wild-reading. The cost is
   one branch per optional-record argument.
