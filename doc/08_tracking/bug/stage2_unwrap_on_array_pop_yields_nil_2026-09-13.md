# BUG: `.unwrap()` on an `Array.pop()` result yields nil in the seed's LLVM native lane

- **Filed:** 2026-09-13
- **Status:** OPEN (2026-09-13)
- **Lane:** BOOT-9 (bootstrap site 10 — the defect immediately behind site 9)
- **Severity:** High — silent nil, no diagnostic. In a DFS drain loop it turns
  into unbounded allocation, which is how it was found.
- **Sibling record:** `stage2_stage3_route_native_compile_timeout_2026-09-13.md`
  (site 9, the `.?` emptiness test). Site 9's fix exposed this one: the same
  loop kept diverging with a correct emptiness test.

## The mechanism, from the runtime source

- `rt_array_pop` (`src/compiler_rust/runtime/src/value/collections.rs:1752-1767`)
  removes the last element and returns it **RAW** — the element value itself,
  never a `Some(...)` enum. It returns `RuntimeValue::NIL` only when the array
  is empty.
- `.unwrap()` lowers to `rt_enum_payload`
  (`src/compiler_rust/runtime/src/value/objects.rs:519-521`), which is
  `get_typed_ptr::<RuntimeEnum>(value, HeapObjectType::Enum).map_or(NIL, ...)`
  — i.e. **nil for anything that is not an Enum heap object**.

So `arr.pop().unwrap()` on an array of tuples/structs asks for the payload of a
value that was never wrapped, and gets nil. `??` would be the right shape
(`rt_unwrap_or_self` handles the raw migration form, and the seed's own
`lower_null_coalesce` says so) — but see the `??` note below.

## Measured — the exact lane that compiles Stage 2

Compiler: the bootstrap's LLVM-capable Rust seed
`src/compiler_rust/target/bootstrap.generations/a5b7f5a40c87.../simple`,
`native-build --backend llvm --runtime-bundle core-c-bootstrap --mode dynload`.
Probe `scratchpad/boot9/probe/drain2.spl`, three drains of the same
`[(i64, bool)]` data, one variable per row:

| form | output |
|---|---|
| A `val (n, f) = a.pop().unwrap()` | `A:;A:;` — **both fields nil** |
| B `val top = b.len()-1; val (n, f) = b[top]; b = b[:top]` | `B8:true;B7:false;` correct |
| C two parallel `[i64]` stacks, index read + slice | `C8:1;C7:0;` correct |

(Each loop carries a `guard < 6` counter; without it, form A does not
terminate.)

## Measured — directly in the Stage-2 candidate

Candidate `ac5a205d9030bea6...` (152198144 B), under gdb on the gate's own
fixture (`scratchpad/boot9/gdb12.sh` + `trace12.gdb`,
`BuildGraph.topological_order`):

```
POP #1 ret=0x8d028b1 ...    PAYLOAD ret=0x3
POP #2 ret=0x8d02941 ...    PAYLOAD ret=0x3
...  (12 consecutive pairs)
```

Every `rt_array_pop` returns a live, distinct heap pointer; every following
`rt_enum_payload` returns `0x3` = `RT_NIL`. The consequence, from a separate
run (`gdb11.sh` + `trace11.gdb`) breaking on the dict insert:

```
SET #1 key=0x3 dict=0x8d02571
...  SET #40 key=0x3 dict=0x8d02571
```

40 consecutive `visited[nil] = true` with the same nil key, so nothing is ever
marked visited and the DFS re-expands forever. VmRSS 40 MB -> 6 GB in 121 s
(`gdb10.rss`), same shape as site 9.

## Lane split, stated rather than smoothed over

The shared Rust seed's **cranelift** lane gets form A RIGHT
(`u8:true;u7:false;`, probe `scratchpad/boot9/probe/popfix.spl`). The LLVM lane
does not. So form A is a backend-visible divergence, not a uniform language
behaviour, and "it works on my engine" proves nothing here. (The `??`
double-evaluation below is NOT lane-specific — it was measured in both.)

The same probe also found that **`??` evaluates its left operand TWICE**, and a
follow-up probe with an iteration counter and length logging
(`scratchpad/boot9/probe/qq.spl`, **LLVM** lane, same seed) isolates it rather
than inferring it:

```
[it1 len_before2 len_after0 n=7 f=false] iters=1
```

One iteration of `val (n, f) = s2.pop() ?? (-1, true)` drops the length by TWO
and binds `7` — the SECOND pop's element. So `??` is not a safe replacement for
`.unwrap()` on a `pop()` (the first probe's single `c7:false;` in the cranelift
lane is the same defect, not a lane quirk), which is why the fix uses the
index-read form. The double evaluation deserves its own record and fix; it is
not scoped to one backend.

## Fix applied (bootstrap blocker only)

`src/compiler/80.driver/driver_build/parallel.spl` — `topological_order` now
reads the top by index and truncates (form B). No language or lowering change.
Guarded by `test/01_unit/compiler/driver/build_graph_topological_order_terminates_spec.spl`.

## Not fixed here

The lowering itself. `.unwrap()` on a raw-form optional should route through
`rt_unwrap_or_self` (or `rt_array_pop` should return a wrapped `Some`), and the
`??` double-evaluation must be settled first, since the two interact. Any such
change lands in the seed's Rust HIR lowering AND the pure-Simple MIR lowering
together, which is out of scope for a bootstrap-unblocking lane.

## Fix implemented 2026-11-09 (verification pending)

**Checked against current policy/design: still valid, re-scoped.** Two of the
three defects above were already fixed on `release/1.0.0` by sibling lanes and
are pinned here rather than re-fixed:

- the nil payload: `.unwrap()` no longer lowers to `rt_enum_payload` on either
  backend; the untyped fallback is `rt_unwrap_or_trap`
  (`codegen/instr/closures_structs.rs`, `codegen/llvm/emitter.rs`), which
  passes a raw present value through and traps on raw nil
  (`unwrap_family_treats_flat_nil_as_present_2026-09-13`);
- `??` double evaluation: `lower_coalesce` binds its subject to one
  `$coalesce_subject` local (`compiler/tests/coalesce_single_evaluation.rs`).

What remained, and what this change fixes, is the typing half of the design
"`pop()` is `T?`, `.unwrap()` on it is the checked unwrap":

- **Seed (Rust HIR):** `pop`/`first`/`last`/`get`/`min`/`max`/`remove` are
  deliberately typed bare `T` by the method result-type table
  (`doc/03_plan/compiler/type_system/seed_hirtype_optional_plan.md` — 547
  direct `.pop()` consumers rely on that today, so retyping them to `T?`
  wholesale is the staged root fix, not this lane). `.unwrap()` on such a
  receiver therefore fell through to dynamic dispatch typed `ANY`. It now
  lowers to `BuiltinCall rt_unwrap_or_trap` typed as the element
  (`hir/lower/expr/mod.rs`, `"unwrap"` arm), so the checked helper runs and
  MIR's name-keyed unbox decodes scalars — the same staging `lower_coalesce`
  already uses for these accessors.
- **Pure-Simple MIR:** already consistent — `pop()` builds a typed Option
  before `rt_array_pop` (`method_calls_literals.spl`), `.unwrap()` branches on
  `rt_is_some` and panics on nil, `??` lowers its operand once
  (`expr_dispatch.spl`). Pinned by a new MIR-level spec.

Tests (TDD — the cargo test was RED before the seed change):

- `src/compiler_rust/compiler/tests/pop_unwrap_checked.rs` (MIR: one
  `rt_unwrap_or_trap`, no dynamic `unwrap`; producer called once under
  `.unwrap()` and `??`; JIT fixture executes).
- `test/fixtures/compiler/pop_unwrap_checked.spl` (executable oracle).
- `test/01_unit/compiler/mir/pop_unwrap_checked_lowering_spec.spl`
  (pure-Simple: one `rt_array_pop`, one `rt_is_some`, `rt_panic`, no
  `rt_enum_payload`; `??` single pop; tuple payload; executed semantics).

The `topological_order` index-read form is retained (now tagged
`@workaround`) until a Stage-2 LLVM-lane build confirms the lowering end to
end; its comment was stale and is corrected.
