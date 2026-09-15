# Module-level `var` write is silently lost when the RHS method reads `me`

- **Filed:** 2026-09-05
- **Host:** macOS arm64 (Darwin 25.5.0)
- **Binary:** `src/compiler_rust/target/bootstrap/simple` (130,402,384 bytes, Sep 5 20:01)
- **Severity:** high — silent data loss in any module that keeps service state
  in a module-level `var`. No error, no warning; the variable simply still
  holds its previous value.

## Symptom

Under the spec runner, `_v = _v.method(...)` where `_v` is a **module-level
`var`** and `method` constructs its result from a field of `me` does not
update `_v`. The call runs, the returned value is correct, and the assignment
appears to happen — but a subsequent read of `_v` returns the pre-call value.

The same code inside `fn main` (no `use std.spec`) behaves correctly, which is
why this hid for so long.

## Minimal reproduction

`build/nb/fixtures/modvar/boxmod4.spl`:

```
class B1:
    n: int
    me inc() -> B1:
        return B1(n: me.n + 1)
    static fn empty() -> B1: B1(n: 0)

var _v1: B1 = B1.empty()

pub fn t1() -> int:
    _v1 = _v1.inc()          # <-- write lost
    return _v1.n

pub fn t4() -> int:
    val cur = _v1            # <-- workaround
    val nxt = cur.inc()
    _v1 = nxt
    return _v1.n
```

Tracked regression spec (RED by design — do not weaken):
`test/01_unit/compiler/module_var_write_lost_when_rhs_reads_me_spec.spl`
plus its fixture `test/01_unit/compiler/fixtures/module_var_me_read.spl`
(mirrored under `test/unit/compiler/`). Measured 2026-09-05:

```
  x keeps the write when the right-hand method reads its own receiver
    expected 1,1,1 to equal 1,2,3
  v keeps the write when the mutation goes through a temporary binding
2 examples, 1 failure
```

The original scratch probes (untracked, `build/` is gitignored) were
`build/nb/fixtures/modvar/boxmod4_spec.spl` and `boxmod5_spec.spl`:

```
expected 1field=11 2field=11 ifbody=11 to equal PROBE      # t1 called twice -> 1, 1
expected tmp_binding=123 plainint=12 to equal PROBE        # t4 called 3x    -> 1, 2, 3
```

`t1()` returns `1` on every call. `t4()` — the same mutation written through a
temporary binding — returns `1, 2, 3` correctly.

## Boundary of the defect (measured)

| shape | persists? |
|---|---|
| `var _n: int`, `_n = _n + 1` | YES |
| `me with_n(v: int) -> Box: return Box(n: v)` (result built from the PARAMETER only), `_b = _b.with_n(_b.n + 1)` | YES |
| `me inc() -> B1: return B1(n: me.n + 1)` (result reads `me`), `_v = _v.inc()` | **NO** |
| same, class with 2 fields | **NO** |
| same, body branches on `if me.n == 0:` | **NO** |
| same, `var st = me` + conditional reassign + `return st` | **NO** |
| `val cur = _v; val nxt = cur.inc(); _v = nxt` | YES |

So the trigger is *the right-hand method reading a field of `me` while the
receiver is the module var itself*. Reading the field at the CALL SITE instead
is fine.

## Real-world impact found

`src/os/apps/smux/api.spl` keeps the whole session/window/pane registry in
`var _svc: ServiceState` and updated it exclusively as `_svc = _svc.add_session(...)`
etc. Every one of those writes was being discarded under the spec runner, so:

- `test/01_unit/os/apps/smux/smux_api_spec.spl` was **4 of 5 RED** on this host
  before any change in this lane (`5 examples, 4 failures`), failing with
  `array index out of bounds: index is 0 but length is 0` because
  `smux_list_windows` returned an empty array after a successful
  `smux_create_session`.
- `smux_detach` returned `false` for a client that had just attached.

Worked around in `api.spl` 2026-09-05 by rewriting all 18 mutation sites into
the temporary-binding form (`val _curN = _svc` / `_svc = _curN.<method>(...)`),
with a comment at the `_svc` declaration pointing here.

## Unblock condition

Fix the interpreter/JIT so a module-level `var` assignment whose RHS reads a
field of the same variable through a method receiver is not discarded (most
likely an aliasing/ordering issue between the receiver load and the store).
Then the temporary-binding workaround in `src/os/apps/smux/api.spl` can be
reverted, and the fixtures under `build/nb/fixtures/modvar/` should be
promoted to a regression spec under `test/01_unit/compiler/`.

## Not yet determined

- Whether the native/JIT path has the same defect (only the seed interpreter
  under the spec runner was exercised).
- Why `fn main` is unaffected.
- How many other modules with module-level `var` service state are silently
  affected. A census of `^var ` in `src/**/*.spl` followed by
  `<var> = <var>\.` call sites would size it.
