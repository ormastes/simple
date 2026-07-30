# `.pop()` on a struct-field array does not shrink the array

- **Found:** 2026-07-30, re-verifying `test/01_unit/lib/editor/document_service_spec.spl`
- **Status:** **RESOLVED 2026-07-30 (lane L-R).** The source fix was already in
  git; the *working copy* had been clobbered back to a pre-fix revision, so every
  binary built from it reproduced the bug. Restoring the file from `HEAD` and
  rebuilding makes all probes green. See "CORRECTION (2026-07-30, lane L-R)".
- **Severity:** silent wrong results. `pop()` returns the correct element, so
  nothing errors — the array just keeps its length.
- **Mechanism (accurate):** the discriminant gate at
  `src/compiler_rust/compiler/src/interpreter_method/mod.rs` — but it is *guarded
  by a `pop` special case in committed source*, which the stale working copy lacked.

## CORRECTION (2026-07-30, lane L-R) — it was a stale working copy, not missing source

The diagnosis of the *mechanism* below is exactly right. The claim that "no
commit fixes it" is **wrong**. `git log -S 'method == "pop"' -- <that file>`
shows the `pop` special case landed in **`f119f8b7120` (2026-07-28 23:58,
`chore: consolidate completed agent session work`)** — a chore-labelled bulk
commit, the exact hazard `.claude/rules/` warns about.

What actually happened:

- `git cat-file -p HEAD:src/compiler_rust/compiler/src/interpreter_method/mod.rs`
  contains the `pop` write-back fix **and** `dec6bc3738f`'s
  `GLOBAL_IMPL_METHODS` enum-static-method fix.
- The **file on disk** contained neither. `git diff` against the untouched
  working copy was `20 insertions, 47 deletions` — the WC was a *rewind* of two
  landed fixes, with nothing new of its own.
- Cargo builds from the working copy, not from `HEAD`. That fully explains the
  engine matrix: the deployed seed (07-29 06:00) and the 07-30 02:33 release
  were built before the clobber and are correct; the 07-29 16:42 debug and the
  07-30 07:47 release were built after it and are broken. It is neither
  debug-vs-release nor a source defect.

**Resolution applied:** `git checkout HEAD -- src/compiler_rust/compiler/src/interpreter_method/mod.rs`,
then `cargo build --bin simple` (debug, 1m17s). No source change was needed or made.
Writing a *new* fix here would have silently reverted `dec6bc3738f`'s enum fix.

**Verification (debug binary rebuilt from the restored file):**

| probe | expected | observed |
|---|---|---|
| `[i64]` field pop | popped=8 len=1 | popped=8 len=1 |
| `[[i64]]` field pop | len=1 | len=1 |
| two-hop `o.inner.zs.pop()` | popped=3 len=2 | popped=3 len=2 |
| local `pop` | popped=3 len=2 | popped=3 len=2 |
| field `clear` / `remove` / `push` | 0 / 1,first=20 / 2 | same |
| field `slice`/`filter`/`map` must NOT clobber receiver | recv unchanged | recv unchanged |
| empty field pop, literal `[10,20,30].pop()` | len=0, popped=30 | same |

`test/01_unit/lib/editor/document_service_spec.spl` → `Results: 15 total, 15 passed, 0 failed`.
`array_coverage` / `array_list_ops` / `array_search_transform` specs are
bit-identical before and after (218/10, 19/0, 33/2) — no regression; those
failures are pre-existing and unrelated.

**Standing lesson:** before diagnosing a Rust-seed behaviour defect, diff the
working copy against `HEAD` for the file you are about to blame. A clobbered WC
presents as a source bug that "no commit fixes".

## Original mechanism analysis (retained — accurate, but the source already guards it)

## Symptom

`arr.pop()` where `arr` is reached **through a struct field** returns the last
element correctly but leaves `len()` unchanged. A plain local array pops fine.

```
struct Box:
    xs: [i64]

fn main():
    var b = Box(xs: [])
    b.xs.push(7)
    print(b.xs.len().to_text())      # 1   (correct)
    val v = b.xs.pop()
    print(v.to_text())               # 7   (correct)
    print(b.xs.len().to_text())      # 1   WRONG, expected 0

    var plain = [1, 2, 3]
    val p = plain.pop()              # 3, len 2 -- correct
```

## ROOT CAUSE

`interpreter_method/mod.rs:1789`, in `evaluate_method_call_with_self_update`:

```rust
let updated_self =
    if MUTATING_METHODS.contains(&method)
        && std::mem::discriminant(&result) == std::mem::discriminant(&recv_val) {
        Some(result.clone())
    } else {
        None
    };
```

The write-back of a mutated receiver is gated on **the method's return value
having the same `Value` discriminant as the receiver**. That guard was added to
stop non-mutating same-type methods (`slice`, `filter`, `map`, `trim`) from
clobbering the receiver — see the comment above the list at mod.rs:1743.

`pop` is the one entry in `MUTATING_METHODS` whose result is **not** the
receiver: it returns the *popped element*. For `[i64]`, `result` is
`Value::Int` and `recv_val` is `Value::Array`, the discriminants differ, so
`updated_self` is `None` and **the mutated array is never written back**.

`push`/`clear`/`remove`/`insert` all return the array itself, discriminants
match, write-back fires — which is exactly why `push` works and `pop` does not.

### Why a plain local array is unaffected

A bare-identifier receiver never reaches that gate. It is served by the
dedicated array-mutator fast path in
`src/compiler_rust/compiler/src/interpreter_helpers/patterns.rs:557`, whose
mutation kernel `apply_array_mutation_in_place`
(`patterns.rs:135-148`) special-cases `pop` explicitly:

```rust
"pop" => Ok(Some(vec.pop().unwrap_or(Value::Nil))),
```

It mutates the `Vec` in place and returns the element separately, so the two
concerns are not conflated. Field receivers never get there.

### Both field-receiver routes hit the same gate

- one hop (`b.xs.pop()`) — `interpreter/expr/calls.rs:133-166`, the two-level
  `FieldAccess` branch. It stashes the field in a `__nested_field_<f>__` temp,
  calls `evaluate_method_call_with_self_update`, and writes the field back
  **only if `updated_self` is `Some`** (calls.rs:160).
- two or more hops (`o.inner.zs.pop()`) — `try_place_receiver_method_call`
  (`interpreter/expr/calls.rs:31-70`), added by the place model
  `61bfb659210`. Same call, and `write_place` is likewise guarded by
  `if let Some(new_self) = updated_self` (calls.rs:86-88).

So a single gate breaks every depth.

## Confirming evidence

Probes run on both a known-good and a known-bad binary. Every result is
predicted by the discriminant gate:

| probe | receiver | `pop` result type | discriminant match | writes back? | observed |
|---|---|---|---|---|---|
| `a.xs.clear()` | field | Array | yes | yes | len 0 — correct on both |
| `a2.xs.remove(0)` | field | Array | yes | yes | len 1 — correct on both |
| `b.ys.pop()`, `ys: [[i64]]` | field | **Array** | **yes** | **yes** | len 1 — **correct on both** |
| `b.xs.pop()`, `xs: [i64]` | field | Int | **no** | **no** | len unchanged |
| `o.inner.zs.pop()` | 2-hop field | Int | no | no | len unchanged |
| `plain.pop()` | identifier | Int | n/a (fast path) | yes | correct |

The nested-array row is the decisive one: **`pop` on a field becomes correct the
moment the popped element happens to be an array**, purely because the
discriminants then match. That is not a plausible signature for UB or for a
`debug_assert`; it is the type-discriminant guard and nothing else.

## Engine matrix — CORRECTED

| Binary | built | struct-field `pop()` | local `pop()` |
|---|---|---|---|
| `bin/release/x86_64-unknown-linux-gnu/simple` (deployed Rust bootstrap seed) | 07-29 06:00 | correct | correct |
| `src/compiler_rust/target/release/simple` | **07-30 07:47** | **len unchanged** | correct |
| `src/compiler_rust/target/debug/simple` | 07-29 16:42 | len unchanged | correct |

All rows with `SIMPLE_EXECUTION_MODE=interpreter`.

### The "Rust debug vs Rust release" framing was WRONG

The earlier revision of this file recorded `target/release` as built 07-30 02:33
and **correct**. That binary has since been rebuilt (07-30 07:47) and now
reproduces the bug. Re-measured on 07-30:

- It is **not** debug-vs-release — the current release build is broken too.
- It is **not** fixed in the newest source — current `main` is broken. No commit
  fixes it.
- It is **not** UB and **not** a `debug_assert`-gated path.

It is an ordinary logic bug in a single `if` condition, present in every build
from current source. The only correct binary is the stale deployed seed.

### Unconfirmed: why the deployed 07-29 06:00 seed is correct

Not explained. Ruled out:

- It is not a pre-place-model binary — `strings -a … | grep 'interpreter/place.rs'`
  hits in all three binaries, so all three contain `61bfb659210`.
- `interpreter_method/mod.rs` and `interpreter_helpers/patterns.rs` have no
  commit since `dec6bc3738f` (07-29 01:58), *before* that seed was built;
  `interpreter/expr/calls.rs` and `interpreter/place.rs` none since
  `61bfb659210` (07-27 22:23). So committed source for the whole path is
  identical between that seed's build time and now.

Most likely the deployed seed was built from a working tree carrying an
uncommitted fix that was never landed (or was lost to a WC clobber — see
`.claude/rules/vcs.md`). **This was not verified** and the deployed binary has no
embedded build sha (`--version` prints only `Simple Language v1.0.0-beta`).
Treat the deployed seed's correctness as unexplained, not as a target to bisect.

## Why it matters more than it looks

`bin/simple test` **spawns the Rust debug binary as its child** (the run log
prints `child binary: .../target/debug/simple`), while `bin/simple run` uses the
deployed seed. So the spec suite exercises an engine that differs from the one
interactive runs use — a spec can go red on correct code, and a real defect can
stay green. Same class as `run_vs_test_harness_divergence_2026-07-28.md`.

Note this divergence is *narrower* than it appeared: the two binaries differ
because one is stale, not because of build profile. Any freshly built binary of
either profile is broken.

## Reproduction

```bash
D=/tmp/pop_repro && mkdir -p $D
cat > $D/pop.spl <<'EOF'
struct Box:
    xs: [i64]

fn main():
    var b = Box(xs: [])
    b.xs.push(7)
    print("after push len=" + b.xs.len().to_text())
    val v = b.xs.pop()
    print("popped=" + v.to_text())
    print("after pop len=" + b.xs.len().to_text())
    var plain = [1, 2, 3]
    val p = plain.pop()
    print("plain popped=" + p.to_text() + " len=" + plain.len().to_text())
EOF

for B in bin/release/x86_64-unknown-linux-gnu/simple \
         src/compiler_rust/target/release/simple \
         src/compiler_rust/target/debug/simple; do
  echo "=== $B"
  SIMPLE_EXECUTION_MODE=interpreter "$B" run $D/pop.spl 2>&1 | grep -E 'len=|popped='
done
```

The discriminating probe (nested array pops correctly, scalar does not):

```
struct A:
    xs: [i64]
struct B:
    ys: [[i64]]

fn main():
    var a = A(xs: [])
    a.xs.push(1)
    a.xs.push(2)
    a.xs.clear()
    print("clear len=" + a.xs.len().to_text())        # 0  correct
    var b = B(ys: [])
    b.ys.push([9])
    b.ys.push([8])
    val e = b.ys.pop()
    print("nested pop len=" + b.ys.len().to_text())   # 1  correct (!)
```

Provenance check that refuted the debug-vs-release framing:

```bash
ls -l --time-style=full-iso bin/release/x86_64-unknown-linux-gnu/simple \
  src/compiler_rust/target/{release,debug}/simple
git log -6 --format='%h %ad %s' --date=format:'%m-%d %H:%M' \
  -- src/compiler_rust/compiler/src/interpreter_method/mod.rs \
     src/compiler_rust/compiler/src/interpreter_helpers/patterns.rs
strings -a <binary> | grep -c 'interpreter/place\.rs'
```

## Workaround (in use)

Index-read the last element and slice-reassign the field — correct on every
engine, because the field is assigned explicitly rather than via write-back:

```
val last_index = handle.undo_stack.len() - 1
val inverse_tx = handle.undo_stack[last_index]
handle.undo_stack = handle.undo_stack.slice(0, last_index)
```

Applied at `src/lib/editor/document/registry.spl` `DocumentRegistry.undo`.

## Fix direction

The discriminant test is a proxy for "did this method mutate the receiver?", and
it is simply the wrong question for `pop`. The receiver must be returned
alongside the result rather than inferred from it.

Minimal, targeted fix at `interpreter_method/mod.rs:1789` — special-case the
methods in `MUTATING_METHODS` whose result is an *element* rather than the
receiver, and write back the receiver as it stands after dispatch:

```rust
// Methods that mutate the receiver but return an ELEMENT, so the
// discriminant proxy below cannot detect them.
const ELEMENT_RETURNING_MUTATORS: &[&str] =
    &["pop", "pop_back", "pop_front", "remove_first", "remove_last", "drain"];
```

...and for those, take the post-dispatch receiver value as `updated_self`.

**Caveat — this requires more than editing the one condition.** The current
dispatch discards the mutated receiver for these methods: `handle_array_methods`
(`interpreter_method/collections.rs:73`) computes `vec.pop()` on a borrowed
slice and returns only the element, so at mod.rs:1789 there is no mutated array
to write back. The dispatch must be changed to surface both. The clean version
is to route field receivers through the existing kernel
`apply_array_mutation_in_place` (`interpreter_helpers/patterns.rs:135`), which
already returns `(mutated vec, Option<popped elem>)` correctly and is documented
as "the single mutation kernel shared by BOTH paths" — the field path is
precisely the caller that does not yet share it. That is the real fix: make the
field-receiver route reuse the identifier route's kernel instead of the
discriminant heuristic.

Per repo policy (`.claude/rules/`), prefer fixing this in pure Simple over the
Rust seed if the pure-Simple interpreter has the same shape; the Rust change
above is the seed-side equivalent. **Not implemented here** — no rebuild was
attempted (diagnosis-only lane).

## Related

- `doc/08_tracking/bug/self_hosted_array_pop_segfault_lex_command_2026-07-29.md`
  — `pop` in the native/codegen lane (`fbb00ce463c` routed bare `pop`/`push`/
  `append` to the array-mutator builtins). Different lane, same primitive.
- `doc/08_tracking/bug/run_vs_test_harness_divergence_2026-07-28.md`
- `doc/08_tracking/bug/module_global_write_lost_on_frame_pop_2026-07-28.md`
