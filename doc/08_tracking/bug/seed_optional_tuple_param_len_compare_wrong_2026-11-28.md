# Seed: `.len() < N` on an optional-tuple-typed parameter is wrong, valid tuple falls to the default

- Found: 2026-11-28, lane S8-K (mqtt `no any` migration). Seed `simple-local-20261128a.exe`.
  Not the same as `rt_tuple_len_unbacked_seed_2026-11-02.md` (that is a missing extern).
- Symptom: with a parameter typed `(i64, i64, text, text)?`, the guard
  `if t == nil or t.len() < 4:` takes the default branch for a valid 4-tuple.
  `print t.len()` on the same value prints `4`, so the length is right but the
  comparison is wrong.
- Repro (prints `-1`, `-2`, `-2`; expected `4`-path value `9` / `4` for a valid tuple):

```
fn a(t: (i64, i64, text, text)?) -> i64:
    if t == nil or t.len() < 4:
        return -1
    t.len()

fn c(t: (i64, i64, text, text)?) -> i64:
    if t.len() < 4:
        return -2
    9

fn main():
    val p = (1, 2, "a", "b")
    print a(p)
    print c(p)
```

- Non-optional `(i64, i64, text, text)` parameter: `t.len() < 4` is correct.
  Untyped parameter: correct.
- Impact: forced the mqtt packet unwrap to use `if val p = packet:` (typed
  `MqttPacket?` struct) instead of a `.len()` guard.
- Fix: seed interpreter comparison of `.len()` result on optional-tuple-typed locals.
