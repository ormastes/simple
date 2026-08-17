# JIT: `text.substring(n).to_int()` chained returns the raw text pointer, silently

Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 02).
**Found:** 2026-08-04

## Symptom

Minimal repro (`build/tmp_gap/sub.spl`, run from the repo root so the relative
path actually compiles — an absolute path makes `simple run` exit 0 without
compiling):

```simple
fn main():
    val arg: text = "--timeout=800"
    print("chained={arg.substring(10).to_int() ?? -1}")
    val s: text = arg.substring(10)
    print("s=[{s}] len={s.len()}")
    print("viaval={s.to_int() ?? -1}")
```

```
$ SIMPLE_TIMEOUT_SECONDS=0 bin/simple run build/tmp_gap/sub.spl
chained=6445613581825          <-- WRONG (and differs run to run: it is a pointer)
s=[800] len=3
viaval=800                     <-- correct

$ SIMPLE_TIMEOUT_SECONDS=0 SIMPLE_EXECUTION_MODE=interpret bin/simple run build/tmp_gap/sub.spl
chained=800                    <-- interpreter is CORRECT
viaval=800
```

Expected: `chained == 800` on both engines.
Actual: under the JIT the chained form yields a large, run-varying i64 — the
heap address of the intermediate text — with **no error, no warning, exit 0**.
Binding the intermediate to a typed `val` first makes it correct, so the value
itself is fine; only the chained lowering is wrong.

`?? -1` does not rescue it: `to_int()` never reports failure here, it returns a
"successful" garbage integer.

## Root cause (proven)

`src/compiler_rust/compiler/src/codegen/instr/methods.rs:131`, inside
`compile_builtin_method`:

```rust
let from_ty = ctx.vreg_types.get(&receiver).copied().unwrap_or(TypeId::I64);
```

`to_int` is matched by the `numeric_cast_target` table a few lines above
(`"to_i64" | "to_int" => Some(TypeId::I64)`), and that block runs *before* the
text-receiver dispatch that would otherwise route to the `rt_string_to_int`
runtime helper (`codegen/instr/calls.rs:2817` and `:3369`,
`codegen/instr/closures_structs.rs:1702`).

When the receiver is a *directly chained* method result — `arg.substring(10)` —
its vreg carries no recorded type, so `vreg_types.get(&receiver)` misses and the
`unwrap_or(TypeId::I64)` default declares the receiver to already be an i64.
The very next branch is

```rust
let converted = if from_ty == to_ty { receiver_val }
```

`from_ty == to_ty == TypeId::I64`, so the cast compiles to **the receiver
unchanged** — the text pointer is handed back as the integer result. Binding to
`val s: text` records `TypeId` for that vreg, the miss does not happen, and the
correct `rt_string_to_int` path is taken.

This is the same failure shape the in-file comment at `methods.rs:110-120`
documents for `to_upper`/`to_utf8` (wildcard arm ⇒ `to_ty == from_ty` ⇒ silent
no-op); that fix corrected the *method-name* matching but left the *unknown
receiver type* default intact, so untyped receivers still collapse onto the
no-op arm.

## Blast radius

Any `<expr producing text>.to_int() / .to_i64() / .to_i32() / .to_u64() / ...`
where the receiver is not a named typed binding. It fails silently with a
plausible-looking integer, which makes it a false-green generator: an assertion
comparing two such values, or any arithmetic on them, will not raise.

One live instance was found and fixed in this lane:
`src/lib/nogc_sync_mut/test_runner/test_runner_args.spl` — the new
`--timeout=N` / `--seed=N` parsing had to be written with an intermediate
`val` (`timeout_value` / `seed_value`) because the chained form parsed
`--timeout=800` as `2363156932769`.

## Why not fixed now

The fix is in the Rust seed's Cranelift codegen, not in `.spl` — the standing
rule is to fix Simple source rather than the seed, and a codegen change here
needs a full Rust rebuild plus a regression sweep across every numeric-cast site
(the `numeric_cast_target` block is on the hot path for all of
`to_u8`…`to_f64`). The correct shape is almost certainly to stop defaulting an
unknown receiver to `TypeId::I64` and instead fall through to the regular
builtin dispatch (which knows how to call `rt_string_to_int`), but proving that
does not regress genuine integer-to-integer casts on untyped vregs is its own
lane.

Workaround until then: bind the intermediate to a typed `val`. Do **not** treat
that as the normal spelling — the chained form is valid Simple and works on the
interpreter.

## Addendum 2026-08-07: defect is method-specific, not chain-shape-generic

Re-probed with a lambda-free minimal repro
(`/tmp/.../scratchpad/probe.spl`, `probe2.spl`) using
`SIMPLE_TIMEOUT_SECONDS=0 bin/simple run <file>` against the currently
deployed `bin/simple` (which prints "this Rust-built Simple binary is a
bootstrap seed only" — i.e. this evidence is about the **Rust seed**, see
binary-identity note below):

```
"  42  ".trim().to_i64()          -> 42   (correct, even chained)
"--timeout=800".substring(10).to_int() -> 5939881247105 (garbage pointer)
"  42  ".trim().to_int()          -> 42   (correct)
"--timeout=800".substring(10).to_i64() -> 6017459030465 (garbage pointer)
```

So the *cast name* (`to_int` vs `to_i64`) is irrelevant — both are equally
broken/fine depending on the **producing method**: `trim()`'s result vreg
gets a type recorded in the seed's `vreg_types` map (so the `to_ty ==
from_ty` short-circuit in `methods.rs:131` does NOT fire and the correct
`rt_string_to_int` path is taken), while `substring()`'s result vreg does
not. This sharpens the root-cause statement above ("its vreg carries no
recorded type" is not a blanket property of *all* chained text methods — it
is specific to which builtin produced the receiver, most likely wherever
`substring`'s codegen path returns without calling
`ctx.vreg_types.insert(...)` for its destination vreg, unlike `trim`'s path).
Not chased further to an exact insert-vs-no-insert line pair in this lane;
the fix direction in "Why not fixed now" above (stop defaulting an unknown
receiver to `TypeId::I64`) still fully covers this, since it does not depend
on which builtin produced the receiver.

**Binary identity / pure-Simple path:** the task that produced this addendum
was asked to fix this in the pure-Simple self-hosted compiler's `.spl`
codegen (`src/compiler/70.backend/backend/cranelift_codegen_adapter.spl`).
That file's `Cast` lowering (`cl_translate_cast`, line ~1150) and its
`operand_type()` helper (line ~1406) are structurally different from the
seed: they read a MIR local's **declared static type** (`local_type(...)`)
rather than a runtime `vreg_types` cache with an `unwrap_or(TypeId::I64)`
default, so the specific failure mode described above (unknown-receiver
defaults to i64) has no obvious analogue there — chained-call result locals
in MIR are typed at construction, not looked up lazily. This could not be
verified end-to-end: the deployed `bin/simple` is the seed (no
`simple.build_stamp` next to it, unlike the SimpleOS target triples), and
the pure-Simple self-hosted candidate on disk
(`bootstrap/stage3/simple`, `bootstrap/stage3/x86_64-unknown-linux-gnu/simple`)
only supports `compile`/`native-build` (no `run`), and `native-build` on a
standalone repro file above failed with `MIR error: unresolved method call:
substring` / `to_int` — it needs the full stdlib-resolution context that
`bin/simple run`/`test` set up, which a bare `native-build` invocation on an
isolated file does not provide. **No `.spl` edit was made** — editing
`cranelift_codegen_adapter.spl` on unverified belief that the pure-Simple
path shares this bug (or editing it and being unable to prove the edit does
anything) would be worse than leaving this open. If this defect needs a
pure-Simple-verified fix, the prerequisite is restoring a working
`bootstrap/stage3` (or freshly-built self-hosted) binary that can execute
`run`/`test` on an isolated file so an A/B is possible.

**Test coverage added:** `test/01_unit/language/text_chained_method_to_int_repro_spec.spl`
covers the trim/substring chained-to-numeric shape via `bin/simple test`
(tree-walk interpreter only — cannot reach the JIT/seed, see
`doc/07_guide/infra/testing.md` "run and test are different engines"). It
passes today (`Results: 3 total, 3 passed, 0 failed`) regardless of whether
this defect is open, and is not a gate for it — the runnable probes above,
via `bin/simple run`, are the real gate.


## 2026-08-17 CORE-P1 triage: DID NOT REPRODUCE / fix present in current source

Verified against CURRENT SOURCE (content, not SHA ancestry) during the crit_01
CORE-P1 sweep. Fix present in current source. `src/compiler_rust/compiler/src/codegen/instr/methods.rs:150` now has the missing STRING branch: `if from_ty == TypeId::STRING && (to_is_int || F32/F64) { let helper = if to_is_int { "rt_string_to_int" } ... }`, with a comment naming this bug doc and the old behaviour ("simply handed back the string HEAP POINTER as a successful integer"). Root cause was NOT unknown receiver type -- the type was known; there are two duplicate method dispatchers and only the sibling in `closures_structs.rs::try_compile_builtin_method_call` had the STRING branch, so this one fell through to a bit-cast.
