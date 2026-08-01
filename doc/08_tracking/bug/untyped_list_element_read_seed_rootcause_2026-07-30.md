# Untyped `list` element-read seed root cause + kafka fallback fix (2026-07-30)

Assignment (leverage play): root-cause and, if contained, fix the untyped-
`list` element-read miscompile IN THE SEED — one codegen fix would retire
all ~750 danger sites named in the previous census pass at once.

## PROVED: precise locus, MIR-dump-confirmed

`src/compiler_rust/compiler/src/mir/lower/lowering_expr_struct.rs`,
`lower_index_expr` (the HIR→MIR lowering for `receiver[index]`
expressions). The unbox decision:

```rust
let element_expr_ty = if expr_ty == TypeId::ANY {
    self.type_registry
        .and_then(|tr| tr.get(receiver_ty))
        .and_then(|ty| match ty {
            HirType::Array { element, .. } => Some(*element),
            HirType::Dict { value, .. } => Some(*value),
            _ => None,
        })
        .unwrap_or(expr_ty)
} else {
    expr_ty
};
...
let needs_int_unbox = matches!(element_expr_ty, TypeId::I8 | I16 | I32 | I64 | U8 | U16 | U32 | U64 | BOOL);
```

and `src/compiler_rust/compiler/src/hir/lower/type_resolver.rs`, bare-name
type resolution:

```rust
"list" => return Ok(self.module.types.register(HirType::Array {
    element: TypeId::ANY,
    size: None,
})),
```

**`list` is not a distinct, unrecognized HIR type variant that falls
through a missing match arm** (that was my first hypothesis and it is
wrong) — it resolves to `HirType::Array { element: TypeId::ANY }`, a
regular array whose element type is explicitly `ANY`. The `element_expr_ty`
match above DOES hit the `HirType::Array { element, .. } => Some(*element)`
arm for it, correctly returning `Some(ANY)`. `needs_int_unbox` is
therefore correctly `false` — the compiler has **no static evidence** the
elements are integers, because `list` is *designed* to hold heterogeneous
values, and the type checker faithfully declined to insert `UnboxInt` on
a type it cannot prove is numeric.

**MIR-dump proof** (`SIMPLE_DUMP_MIR=get_via ./bin/simple probe.spl`,
minimal pair `fn get_via_list_param(l: list, i: i64)` vs
`fn get_via_typed_param(l: [i64], i: i64)`, both bodies `l[i] & 0xFF`):

```
[MIR-DUMP] function: get_via_list_param
    Call { dest: Some(VReg(4)), target: Pure("rt_array_get"), args: [...] }
    ConstInt { dest: VReg(5), value: 255 }
    BinOp { dest: VReg(6), op: BitAnd, left: VReg(4), right: VReg(5) }
    -- no UnboxInt --

[MIR-DUMP] function: get_via_typed_param
    Call { dest: Some(VReg(4)), target: Pure("rt_array_get"), args: [...] }
    UnboxInt { dest: VReg(5), value: VReg(4) }
    ConstInt { dest: VReg(6), value: 255 }
    BinOp { dest: VReg(7), op: BitAnd, left: VReg(5), right: VReg(6) }
```

Executed output: `10` (typed, correct) vs `80` (list, `10<<3`) — matching
every `<<3` symptom from passes 7/8 exactly.

## Not the DECODE_INT sign-extension family (63b7ae7753d)

That commit fixed a **wrong-shift-direction** bug (logical `>>3` instead
of arithmetic, corrupting only negative boxed integers) in the C runtime's
`DECODE_INT` macros on freestanding/hosted paths. This bug is different
in kind: the decode is **skipped entirely** for `list`-typed reads (no
shift of either direction is applied), and it lives in the Rust seed's
MIR lowering (a compile-time decision about whether to emit `UnboxInt`),
not the C runtime's unbox macro itself. The two are siblings in the same
boxing/tagging subsystem, not the same defect — worth cross-referencing,
not conflating.

## INFERRED: why a safe general fix is NOT contained this pass

Per the assignment's caution ("untyped list may legitimately hold
heterogeneous values... mirror the interpreter's contract, don't assume
all-i64") — this is not a hand-wave, it is the actual, structural reason
a general fix is deep:

- `list`'s `HirType::Array { element: ANY }` representation means the
  *type system itself* has no per-list, per-call-site knowledge of
  content. A given `list`-typed function parameter can legitimately be
  called with all-integer content at one call site and mixed content at
  another; the compiler compiles ONE function body, so any static
  decision to "just always unbox as i64" would be **wrong and unsafe**
  for a genuinely heterogeneous list (unboxing a non-integer tagged value
  — e.g. a heap pointer to a string/struct — with an integer arithmetic-
  shift-right is a type-confusion bug, not just a wrong-value bug; it can
  hand later code a garbage address).
- The interpreter gets this right because it is a tree-walker that
  inspects each `RuntimeValue`'s tag bits **dynamically, per element, at
  the point of use** — not a static, compile-time, per-callsite decision.
  Replicating that correctly in the JIT/native codegen path requires
  either (a) a new runtime-tag-dispatched "smart decode" primitive
  invoked at every consumption site of an `ANY`-typed value that
  downstream code treats as numeric (arithmetic, bitwise ops, assignment
  to a typed local) — a cross-cutting change touching many lowering
  sites, not a one-line fix to `lower_index_expr` — or (b) a much bigger
  compiler feature (call-site monomorphization/specialization of
  `list`-typed parameters based on actual argument element types), which
  is a new capability, not a bug fix.
- Landing either untested in one session risks shipping a **worse**
  regression than the status quo: a plausible-looking "always unbox"
  patch would silently corrupt any genuinely heterogeneous `list` usage
  elsewhere in this ~1257-site surface that I have not audited for
  content-homogeneity, in exchange for fixing the (very real, dominant)
  cases where `list` is used as a de facto homogeneous byte/int buffer.

**Conclusion**: documented per the assignment's own fallback trigger —
the mechanism is real, precisely located, and not safely containable in
this pass. Falling back to the kafka dedup retype (first item of the
pass-9 census's disclosed fix order) to ship verified value.

## Fallback fix landed: kafka `serialization.spl` (3 byte-identical layout tiers)

`src/lib/{gc_async_mut,nogc_async_mut,nogc_sync_mut}/kafka/serialization.spl`
(pass-9 census confirmed these 3 are byte-identical; a 4th path,
`gc_sync_mut/kafka/serialization.spl`, is a thin re-export facade
`export use std.gc_async_mut.kafka.serialization.*`, not a real 4th copy
— no fix needed there). Retyped all 11 `list`-typed sites to `[i64]`
(byte-value semantics throughout — varint bytes, CRC32 table entries,
int32/int64 byte arrays, UTF-8 wire bytes — homogeneous i64 by
construction, satisfying the heterogeneity caution above): `encode/
decode_varint_{un,}signed`, `crc32_table`, `int32/int64_to_bytes`,
`bytes_to_int{32,64}`, `serialize/deserialize_string`.

**A real live-site consequence, found and fixed**: `bytes_to_int32` reads
`bytes[0..3]` directly via bracket index (no `.get()`), independently
confirming the pass-3 finding (`bytes_to_int32` misdecoding 5 as 40) is
not specific to `.get()` — the same `list`-parameter shape corrupts
bracket-index reads too, exactly as passes 7/8 established.

**Module-resolution pitfall hit during verification**: a probe using the
bare `use kafka.serialization.{...}` import (no `std.<family>.` prefix,
matching the file's own `import kafka.types`) initially still showed the
bug under the default engine *after* only `gc_async_mut`'s copy was
fixed — the bare `kafka.X` path resolves through a family-default
mechanism that did not pick the tier I had edited first. Syncing the
identical fix to all 3 real copies made the ambiguity moot and the probe
then matched expectations under both engines. Anyone doing family-tiered
kafka fixes one-tier-at-a-time should sync all 3 before trusting a
bare-import probe.

## Verification (both engines, independent references, vacuity)

```
                          DEFAULT (pre-fix)   DEFAULT (post-fix)   INTERPRET (post-fix)
varint(300)  decode          2144                 300                   300
varint(128)  decode          1024                 128                   128
svarint(-150) decode         1068                -150                  -150
int32_rt(32)                  256                  32                    32
int32_rt(305419896)      2443359168           305419896             305419896
int64_rt(4886718345)    39093746760          4886718345            4886718345
str_rt("hello")               ""               "hello"               "hello"
str_rt("café")                ""                "café"                "café"
```

All post-fix values verified against independently-derivable references
(varint/int32/int64 are self-describing round-trips; the specific values
chosen include multiples of 32, matching base58's own `<<3`-collision
regression class, and 0x12345678 as a recognizable byte-order canary).
All post-fix values are byte-identical under `SIMPLE_EXECUTION_MODE=interpret`
too — no residual engine divergence.

**Vacuity**: original (pre-fix) code, same probe, default engine —
reproduces every failure above (`2144` instead of `300`, empty strings,
etc.), confirming the fix is real, not a probe artifact.

## Separate, pre-existing, out-of-scope bug found (not fixed)

`crc32_table()` defines only 64 entries, but `crc32_calculate` indexes it
with `table_idx = (crc ^ byte_val) % 256` (range 0-255). Under
`SIMPLE_EXECUTION_MODE=interpret` this is a hard, bounds-checked crash
(`array index out of bounds: index is 206 but length is 64`); under the
default engine it silently reads out-of-bounds memory and returns a wrong
CRC (`4294967292` instead of the independently-computed
`3421780262` = `binascii.crc32(b"123456789")`). This is unrelated to the
`list`/`[i64]` typing question — it is a genuinely incomplete CRC32 table
(needs the full standard 256-entry IEEE CRC32 lookup table, not the 64
present) — and out of scope for this pass. Flagging for a follow-up; not
fixed here.

## Recommended next steps (unchanged from the pass-9 census, now partially executed)

1. Kafka: `serialization.spl` done (this pass, all 3 tiers). `types.spl`
   (54 sites/tier), `protocol.spl` (47), `consumer.spl` (46),
   `producer.spl` (12), `utilities.spl` (4) remain — same byte-identical-
   across-3-tiers structure, same mechanical `: list` → `[i64]`/`[u8]`
   retype pattern, not attempted this pass (time-bounded).
2. `crc32_table` 256-entry fix — separate bug, separate pass.
3. Post-quantum / classical asymmetric / hash-KDF / auth-token / AES tiers
   — unchanged from the pass-9 census fix order.
4. Compiler-side direction (unchanged, now with concrete evidence behind
   it): promoting a lint/error for `: list`-typed function parameters
   (steering toward the proven-safe concrete element types) is more
   tractable and lower-risk than a general runtime-tag-dispatched decode
   mechanism, given the demonstrated type-confusion risk of the latter.

## Re-measurement 2026-08-01 (base `9349ff90f60`, deployed seed)

Re-ran the three recorded members of this family as a single no-import probe
(an import forces a whole-module interpreter fallback and makes the run
silently vacuous). Probe values avoid `3` (the nil sentinel); the corruption
signature is `v -> v*8`, so `5 -> 40` and `7 -> 56` are the tells.

Default engine (Cranelift JIT) vs `SIMPLE_EXECUTION_MODE=interpret`:

| probe | default | interpret | verdict |
|---|---|---|---|
| `ctl_direct` — straight-line `[i64]` read | `5,7` | `5,7` | control passes |
| `param_untyped` — callee param declared `: list` | **`40,56`** | `5,7` | **STILL LIVE — exact `<<3`** |
| `param_typed` — callee param declared `[i64]` | `5,7` | `5,7` | unaffected, confirms the retype workaround |
| `rebind_from_empty` — `var work = []` then rebind | `5,7` | `5,7` | **does NOT reproduce** |
| `rebind_from_nonempty` (control) | `5,7` | `5,7` | unaffected |
| `loop_spill_buf0` — `.push()` in a `while`, index-read later iteration | `5;5;5;5;5;5;` | same | **does NOT reproduce** |
| `loop_presized_buf0` (control) | `5;5;5;5;5;5;` | same | unaffected |

**PROVED:** the untyped `: list` parameter member (family member 3) is live at
this base, with the exact documented `<<3` signature and the documented
interpreter/default polarity reversal.

**NOT REPRODUCING at this base** in the shapes recorded on 2026-07-29:
the empty-list-first-assignment poisoning (member 1) and the loop-carried
`.push()` spill (member 2). Both returned correct values on both engines.
This is *not* proof they are fixed — the original repros were shrunk from
`base58_decode` and the shapes here may not be faithful. Treat as "not
reproducible from the recorded description"; re-derive from the base58 original
before either closing them or re-asserting them.

Consequence for the fix order: the `: list` retype campaign remains the only
member with a demonstrated live reproduction, which strengthens recommended
next step 4 above (lint/error on `: list` parameters) relative to the
general runtime-tag-dispatched decode.
