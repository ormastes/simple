# Native/JIT: tagged nil reaching an i64 sink prints as the integer `3`

- **Status:** representative path FIXED 2026-08-18 (Cranelift render routing); other i64 sinks listed below still open
- **Severity:** silent wrong answer — a missing/absent value is byte-identical to a legitimately stored `3`
- **Related:**
  - `doc/08_tracking/bug/native_dict_f64_get_nil_sentinel_collides_with_stored_3_2026-08-17.md` (same sentinel, `f64` sink)
  - `doc/07_guide/language/dict_native_pitfalls.md`
  - `rt_array_at` doc comment, `src/compiler_rust/runtime/src/value/collections.rs:715-760`

## 1. Reproduction — no missing extern involved

The defect was first noticed via an unimplemented extern (`got 3`), but it is
independent of that fabrication bug. Fixture (`Dict<str, i64>` miss):

```
fn main():
    val d: Dict<str, i64> = {"k": 7}
    val hit: i64 = d["k"]
    print "hit: {hit}"
    val miss: i64 = d["nope"]
    print "miss: {miss}"
    val three: i64 = 3
    print "literal-3: {three}"
```

Binary identity (per `.claude/rules/commands.md`):

```
/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple
59620392  2026-08-18 01:08:42  (the Rust seed)
```

Measured, verbatim:

| line | `SIMPLE_EXECUTION_MODE=interpret` (oracle) | `SIMPLE_EXECUTION_MODE=jit` |
|---|---|---|
| `hit:` | `7` | `7` |
| `miss:` | **`nil`** | **`3`** |
| `literal-3:` | `3` | `3` |

`miss` and `literal-3` are indistinguishable on the JIT lane.

## 2. Mechanism

`SIMPLE_DUMP_MIR=main` on the fixture:

```
Call { dest: VReg(21), target: Pure("rt_index_get"), args: [...] }
UnboxInt { dest: VReg(22), value: VReg(21) }
Store { addr: VReg(23), value: VReg(22) }          ; local slot 2
Load  { dest: VReg(25), addr: VReg(26) }           ; local slot 2
Call  { dest: VReg(27), target: Pure("rt_raw_i64_to_string"), args: [VReg(25)] }
```

- `rt_index_get` on a miss returns `RuntimeValue::NIL`, whose word is `3`
  (`TAG_SPECIAL=0b011 | SPECIAL_NIL=0`).
- `UnboxInt` lowers (`codegen/instr/mod.rs`) to `rt_value_unbox_int`, documented
  as **total**: `TAG_INT` shifts by 3, *everything else passes through
  verbatim*. So `NIL` survives as the raw word `3` in an i64-typed vreg.
- The render sink is `rt_raw_i64_to_string`, which formats any word as a plain
  signed integer → `"3"`.

## 3. Intended contract — already implied by the code, not invented here

Two existing precedents settle it; neither is new policy.

- **Producer side: (c) impossible by construction.** `rt_array_at`'s doc comment
  refuses to return the "raw migration form" precisely because "the nil sentinel
  IS the untagged word 3 … so a raw optional holding the value 3 would be
  indistinguishable from absence BY CONSTRUCTION", and returns a boxed `Option`
  instead.
- **Render side: (b) print as `nil`.** `rt_opt_i64_to_string`
  (`runtime/src/value/sffi/io_print.rs:376`) already exists for exactly the raw,
  untagged may-be-nil representation and renders the word `3` as `nil`, with an
  explicit note that a genuine payload of 3 is an accepted, documented limit.
- The tree-walking interpreter, the reference oracle, prints `nil`.

Option (a), a hard error, is ruled out by the `f64` sibling fix, which
deliberately *preserved* nil so `== nil` and `?? default` keep working.

So: the value must not be decoded into a bare i64 at all (producer), and where
it already has been, it must render as `nil` (sink). Nothing at an i64 sink can
decide from the bit pattern alone — `3` is ambiguous by construction — so the
discrimination has to be carried as **provenance**.

## 4. Fix implemented (one representative path)

`src/compiler_rust/compiler/src/codegen/instr/mod.rs` +
`.../instr/body.rs` — nil provenance in the Cranelift emitter.

**A first attempt that was measured and rejected**, recorded because it is the
obvious wrong answer: route a "tainted" operand to the already-existing
`rt_opt_i64_to_string`, which renders the word 3 as `nil`. That builds and fixes
the miss, but it merely *flips which side is wrong* — measured on a
`Dict<str,i64>` holding `three=3`, the JIT then printed `three: nil`. The raw
word after the decode genuinely carries no information; no sink-side rule can
work.

**What is implemented instead:** capture the discrimination *before* the decode
destroys it. A stored 3 arrives at `UnboxInt` as the TAGGED word 24; a miss
arrives as the TAGGED word 3. So:

- `UnboxInt` emits `is_nil = (tagged_input == 3)` as an i8 SSA value and records
  it against its dest in `InstrContext::nil_tainted`
  (`VReg -> (BlockId, Value)`), alongside `::nil_tainted_locals` for slots.
- The flag follows the value through local-slot `Store`/`Load` — MIR routes the
  value through a local before the sink reads it back. Storing a value with no
  flag clears the slot's.
- At `MirInst::Call` on `Pure("rt_raw_i64_to_string")` whose single operand
  carries a flag *recorded in the current MIR block*, the numeric result is
  `select`ed against a literal `"nil"` string. The same-block condition keeps the
  SSA value trivially dominating; a cross-block operand falls back to today's
  behaviour rather than emitting invalid IR.

A literal `3` never flows through `UnboxInt`, so it has no flag and still prints
`3`. No runtime change was needed.

### Measurement, after (same binary discipline)

```
/mnt/data/cargo-niltag/release/simple   59589368  2026-08-18 03:43:49
```

| fixture | interpret (oracle) | jit before | jit after |
|---|---|---|---|
| `d["nope"]` miss | `nil` | `3` | `nil` |
| `d["k"]` hit = 7 | `7` | `7` | `7` |
| literal `3` | `3` | `3` | `3` |
| `d["three"]` hit = 3 | `3` | `3` | `3` |
| `d["big"]` = i64::MAX | `9223372036854775807` | same | same |
| `d["neg"]` = -7 | `-7` | same | same |

JIT now matches the oracle on every line of both fixtures.

**Verification scope, stated honestly:** the two fixtures above, plus a clean
`cargo build --release --bin simple` in an isolated `CARGO_TARGET_DIR`
(`/mnt/data/cargo-niltag`). The repo test suite was NOT run for this change, and
nothing was deployed over `bin/simple`.

**Confound, recorded rather than hidden:** this is a shared worktree with several
concurrent agent sessions. At measurement time `git diff --stat src/compiler_rust`
showed 49 modified files; only two of them are this change
(`codegen/instr/mod.rs`, `codegen/instr/body.rs`). The before/after runs used the
same tree apart from this change's own delta, so the differential is valid, but
the absolute behaviour of that binary is not attributable to this change alone.

## 5. Sites NOT changed (deliberately listed, not half-fixed)

The taint is only *consumed* at the one representative render sink. Other i64
sinks that can receive an undecoded sentinel and are still open:

- `rt_raw_u64_to_string` — the unsigned twin of the fixed sink.
- Integer **arithmetic** on a tainted vreg (`BinaryOp`): `miss + 1` yields `4`
  with no diagnostic. The `f64` sibling bug has the same shape.
- Comparisons other than the `== nil` form that MIR lowering retargets.
- Returning a tainted i64 across a function boundary — taint is per-function and
  is not propagated into callers or through block parameters.
- The LLVM backend (`codegen/llvm/**`) has an independent lowering and was not
  touched.

Closing these properly means the producer-side fix (`(c)`: never decode a
may-be-nil value into a bare i64 in the first place, per `rt_array_at`), which
is a MIR-lowering change outside this change's scope.

## 6. Interaction with the `f64` record

No collision. The `f64` fix lives in `MirInst::UnboxFloat` and encodes nil as the
`f64` whose *bits* are `3` (a denormal that no ordinary computation produces),
with the nil comparison retargeted onto the same constant. That trick is
unavailable for `i64` — `3` is an ordinary integer, so the `i64` domain has no
spare bit pattern, which is exactly why this fix is provenance-based rather than
value-based. The two changes are in different match arms and touch disjoint
runtime helpers (`rt_value_as_float` vs `rt_raw_i64_to_string`).
