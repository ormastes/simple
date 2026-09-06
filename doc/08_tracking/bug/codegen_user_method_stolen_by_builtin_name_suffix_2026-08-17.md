# Codegen: a user method whose name matches a builtin string method is stolen outright (returns 0)

Status: RESOLVED in tree 2026-08-17 (fix at `closures_structs.rs:557`, verified
on an isolated rebuild; NOT yet in the deployed `bin/simple`) — see the last
section.
Date: 2026-08-17
Severity: high (silent wrong result — compiles clean, exits 0)
Found by: the class-detection probe written for
`interp_me_method_first_param_times8_conditional_2026-06-29.md`

## Symptom

A user-defined method on a plain struct whose NAME matches a builtin string
method is not called at all — the JIT substitutes the runtime helper.

```spl
struct Collider:
    tag: i64

impl Collider:
    me char_code_at(v: i64) -> i64:
        v

fn main():
    print(Collider(tag: 0).char_code_at(42).to_text())
```

Observed (`SIMPLE_EXECUTION_MODE=jit bin/simple run`): `0`. Expected: `42`.
`SIMPLE_EXECUTION_MODE=interpreter`: `42` (correct). Exit code 0 in both cases.

Measured on `bin/release/x86_64-unknown-linux-gnu/simple` (59,536,728 bytes,
mtime 2026-08-16 22:59) AND on a seed rebuilt from current source
(`/mnt/data/cargo-target-c1b-a/release/simple`, 2026-08-17) — so it is live in
tree, not an artefact of a stale binary.

## Relationship to the append/push defect

Same FAMILY, different mechanism, and the distinction matters:

- `push`/`append` (FIXED 2026-08-17, `mir/lower/lowering_expr_method.rs:1606`):
  the user method WAS called, but MIR rewrote its first integer argument
  (tag-boxed it, `v << 3`), so the callee read `value * 8`.
- `char_code_at` (THIS bug): the user method is not called at all. The receiver
  is typed (`Collider`), so the qualified name `Collider.char_code_at` is formed
  correctly, but codegen's qualified-name **suffix** resolution maps the part
  after the last `.` through a name table to `rt_string_char_code_at`, which
  fails closed with 0 on a non-text receiver.

The "likely sites" below were the original hypothesis. **They are wrong — see
the localization section at the bottom (2026-08-17, later same day), which
identifies the actual single site by experiment.**

Likely sites (name tables keyed on the method suffix, no receiver check):
- `src/compiler_rust/compiler/src/codegen/instr/calls.rs` (~:3450-3520,
  `if let Some(dot_pos) = func_name.rfind('.')` -> `match method_part`)
- `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs` (~:1788+,
  `let runtime_func = match method`)

Related prior filing: `codegen_bare_method_receiver_type_blind_candidate_selection_2026-07-28.md`
covers the erased-receiver half of this; this row is the TYPED-receiver half,
which that doc's fix does not reach.

## Scope not established

Only `char_code_at` was measured. The class probe round-trips 20 builtin names
and the other 19 pass, but the probe uses a single `(i64) -> i64` shape and does
not vary arity or argument type, so a same-named user method with a different
signature may fail for names that pass here. A census of user-defined methods in
the tree whose names collide with the codegen name tables has NOT been done.

## Regression coverage (already in tree)

`test/01_unit/compiler/codegen/probe_builtin_name_collision_arg_transport_jit.spl`
checks this case on a dedicated `KNOWN-OPEN` verdict line
(`BUILTIN_NAME_COLLISION KNOWN-OPEN COUNT: 1`), asserted by
`test/01_unit/compiler/codegen/builtin_name_collision_arg_transport_spec.spl`.
That count must drop to 0 when this is fixed, and the spec fails if a NEW
known-open appears — so this cannot be silently dropped or silently grow.

## Fix direction

Gate each suffix-table substitution on the receiver's static type actually being
the builtin the helper belongs to (text / array / dict), exactly as
`lowering_expr_method.rs` now gates `push`/`append` and already gated
`index_of` on `receiver_is_array`. Fall through to normal name resolution when
the receiver is a user type that defines the method.

## Localization 2026-08-17 (later same day) — EXACT SITE, still OPEN (Rust seed)

Binary identity: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
**59537240 bytes, mtime 2026-08-17 12:58:51** (Rust seed, rebuilt this day).

### Re-reproduced, verbatim

Fixture `cc.spl` is the exact source in the Symptom section above.

```
$ SIMPLE_EXECUTION_MODE=jit        bin/simple run cc.spl   ->  0
$ SIMPLE_EXECUTION_MODE=interpreter bin/simple run cc.spl   ->  42
```

### The suffix-table hypothesis is DISPROVEN

The same fixture was re-run with the method renamed to four OTHER names that
are ALSO in both suffix tables named above (`calls.rs:3461+`,
`closures_structs.rs:1793+`), plus one control:

```
$ for m in char_code_at2 byte_at trim join write_span; do
    sed "s/char_code_at/$m/g" cc.spl > cc_$m.spl
    printf "%s => " "$m"
    SIMPLE_EXECUTION_MODE=jit bin/simple run cc_$m.spl 2>/dev/null | tail -1
  done
char_code_at2 => 42
byte_at => 42
trim => 42
join => 42
write_span => 42
```

`byte_at`, `trim`, `join` and `write_span` all sit in the very same `match
method_part` / `match method` tables as `char_code_at` and all four resolve to
the USER method correctly. So those tables are NOT the mechanism — they are
reached only after `ctx.func_ids.get(func_name)` misses, and for a typed
receiver it does not miss.

### Actual root cause — one hard-coded, receiver-blind special case

`src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:557-565`,
inside `compile_method_call_static` (fn starts at :519):

```rust
if lookup_name.ends_with(".char_code_at") {
    if let Some(result) = try_compile_builtin_method_call(ctx, builder, receiver, "char_code_at", args)? {
        if let Some(d) = dest {
            ctx.vreg_values.insert(*d, result);
        }
        return Ok(());
    }
}
```

This is a bare suffix test on the QUALIFIED name, with **no receiver-type
check at all**, and it is placed **before** every resolution path in the
function — before the `bare_builtin_collection` block (:594), before
`allow_qualified_builtin` / `prefer_builtin_first` (:608-655, which *are*
receiver-type gated), and before the `ctx.func_ids` / `_dot_` lookups. So
`Collider.char_code_at` ends with `.char_code_at`, the guard fires, the builtin
is emitted against a non-text receiver, `rt_string_char_code_at` fails closed
with 0, and the user's `impl` body is never reached. `char_code_at` is the ONLY
method with such an unconditional pre-resolution hook, which is exactly why it
is the only one of the five probed names that fails.

Every *other* char_code_at site in the seed is already correctly gated and is
NOT implicated:
- `mir/lower/lowering_expr_method.rs:1397` — gated on `receiver.ty == TypeId::STRING`.
- `mir/lower/lowering_expr_method.rs:167` — gated on `effective_ty == TypeId::STRING`.
- `hir/lower/expr/mod.rs:938` — return-type fallback, gated on STRING/ANY.
- `codegen/llvm/mod.rs:80-98` (`resolved_text_runtime_method`) — requires a
  canonical builtin OWNER, and has a unit test asserting `UserText_dot_char_code_at`
  is NOT redirected.

### Fix direction (unchanged in spirit, now precise)

Gate the `:557` block the same way its neighbours are gated: require
`ctx.vreg_types.get(&receiver)` to be `TypeId::STRING` (or absent/ANY, i.e. an
erased receiver, which is the case the hook was presumably added for). A typed
user receiver must fall through to normal resolution.

**Not fixed here:** this is Rust seed code (`src/compiler_rust/**`), and this
lane's mandate for seed defects is to localize and record rather than to change
and ship an unverifiable binary. The one-line gate above is the whole change; it
needs a seed rebuild plus a re-run of the two probes to be claimed as fixed.

**Status: OPEN**, root-caused to a single line, re-reproduced 2026-08-17 on the
12:58 seed.

## FIX APPLIED AND VERIFIED 2026-08-17 (20:1x) — RESOLVED in tree, NOT yet deployed

### Step 1 — re-reproduced on the newly redeployed seed

`bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`, md5
`669150b61f2f20401a6a895ae54e9fee`, size 59550432, mtime 2026-08-17 20:10:45.

```
$ for m in jit interpreter; do SIMPLE_EXECUTION_MODE=$m bin/simple run <scratch>/cc.spl; done
jit => 0
interpreter => 42
```

Still RED on the redeploy — the rebuild carried no change to this site.

### Step 2 — the recorded one-line gate, applied

`src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:557` — the
unconditional `lookup_name.ends_with(".char_code_at")` hook is now gated on the
receiver's vreg type:

```rust
let ccat_recv_ty = ctx.vreg_types.get(&receiver).copied();
let ccat_receiver_ok = match ccat_recv_ty {
    None => true,
    Some(t) => t == TypeId::STRING || t == TypeId::ANY,
};
if ccat_receiver_ok && lookup_name.ends_with(".char_code_at") {
```

A typed user receiver (`Collider`) now falls through to normal resolution; an
erased/ANY or STRING receiver still takes the builtin path unchanged.

### Step 3 — rebuilt in an ISOLATED target dir and verified

```
$ cd src/compiler_rust && CARGO_TARGET_DIR=/mnt/data/cargo-target-verify-ccat \
    cargo build --release --bin simple
    Finished `release` profile [optimized] target(s)
$ md5sum /mnt/data/cargo-target-verify-ccat/release/simple
fe852b91fde8886e9eed080b1487b22b   (59619744 bytes, 2026-08-17 20:17)

$ V=/mnt/data/cargo-target-verify-ccat/release/simple
$ for m in jit interpreter; do SIMPLE_EXECUTION_MODE=$m $V run <scratch>/cc.spl; done
jit => 42          <-- was 0
interpreter => 42

# the four sibling suffix-table names + control, all still correct
char_code_at2 => 42   byte_at => 42   trim => 42   join => 42   write_span => 42

# NO REGRESSION on a real text receiver ("ABC".char_code_at(1) == 66):
jit => 66
interpreter => 66
```

**Verdict: RESOLVED (fix in tree, verified on a purpose-built binary).** The
verification binary was deliberately NOT deployed over `bin/simple` — other
lanes are using it — so the defect will still reproduce on the deployed seed
until the next redeploy. Not committed by this lane.
