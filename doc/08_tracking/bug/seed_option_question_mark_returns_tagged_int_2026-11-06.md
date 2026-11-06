# Seed `run`: `?` on an `Option<i64>` yields the tagged word (value * 8)

- Found: 2026-11-06, XRay PR5b (`work/xray-aarch64-runtime-20261106`), aarch64 Linux.
- Affects: Rust seed `run` (both the Nov-5 shared seed
  `src/compiler_rust/target/bootstrap/simple` and a seed built from this branch).
  The same function returned the right value under `test` in a spec, so the
  difference is in the `run` engine (the run reports
  `[engine-demotion] reason=hybrid-interp-splice`).
- Status: open. Workaround in `src/lib/nogc_sync_mut/trace/xray_native_module_v1.spl`
  (`xray_hex_v1` returns a -1 sentinel instead of `i64?` + `?`).

## Repro

```simple
fn h(x: i64) -> i64?:
    Some(x)

struct P:
    a: i64

fn k() -> P?:
    val v = h(5)?
    Some(P(a: v))

fn main():
    print "k_a={k().unwrap().a}"
main()
```

`simple run repro.spl` prints `k_a=40`; expected `k_a=5`. 40 = 5 << 3: the
unwrapped payload is the runtime's tagged integer word, not the integer.

## Impact seen

`/proc/self/maps` addresses parsed through `?` came out 8x too large; the
next raw memory read SIGSEGV'd the process. A silent wrong value, not an error.

## Fix direction

The `?` lowering for `Option` in the seed's run engine must untag the payload
exactly like `match Some(v)` / `.unwrap()` do. Add the repro as a seed
regression test.
