# `rt_enum_discriminant` / `rt_enum_check_discriminant` are enum_id-blind name hashes

- **Date:** 2026-08-08
- **Status:** OPEN (latent trap — no live defect found in the current tree)
- **Severity:** latent silent-miscompile class; builds cleanly, wrong at runtime
- **Component:** `src/compiler_rust/runtime/src/value/objects.rs`, `.spl` compiler backends

## Summary

`rt_enum_discriminant(v)` returns `hash_variant_discriminant(<variant name>)` — Rust
`DefaultHasher` over the *variant name string*, truncated to 32 bits. It does **not**
incorporate the enum's identity. `rt_enum_check_discriminant(v, expected)` has the same
blindness: it compares only the discriminant field.

Consequence: **two different enums that share a variant name produce identical
discriminants.** `AlphaOp.Add` and `BetaOp.Add` are indistinguishable by
`rt_enum_discriminant` even though `rt_enum_id` differs. Any code that compares a
discriminant against a value derived from a *different* enum family silently takes the
wrong branch, with no build error.

The repo has many collision-eligible families in active use with these externs:
`MirBinOp`, `MirUnaryOp`, `HirUnaryOp`, `UnaryOp`, `MirTypeKind`, `HirTypeKind`,
`TypeKind`, `MirInstKind`, `HirExprKind`, `HirStmtKind`, `StmtKind`, `VariantKind`,
`LocalKind`, `MethodResolution`. Names like `Add`, `Sub`, `Mul`, `Eq`, `Not`, `Named`,
`Tuple` recur across several of them.

Secondary risk: the 32-bit truncation of SipHash means unrelated variant names can
collide by birthday even without sharing a name.

## Measured truth table

Probe: payload-less enum + payloaded enum, positive control `rt_enum_discriminant(42)`
(must return `-1` — the runtime returns `-1` for any non-`HeapObjectType::Enum` value,
so a non-`-1` here would mean the extern was not actually reached).

Lanes measured: `bin/simple run` (JIT, default) and `SIMPLE_EXECUTION_MODE=interpret`.
Two separate processes each. All values identical across runs and across both lanes.

| expression | disc | note |
|---|---|---|
| `rt_enum_discriminant(42)` | `-1` | positive control fires |
| `PayloadLess.Add` | `465620071` | stable across runs |
| `PayloadLess.Sub` | `3803938095` | stable |
| `PayloadLess.Eq` | `810919283` | stable |
| `Payloaded.Ca(1)` | `1457792540` | stable |
| `Payloaded.Cc(1)` | `1268591969` | stable |
| `AlphaOp.Add` | `465620071` | id `470242188` |
| `BetaOp.Add` | `465620071` | id `1936511466` — **COLLISION** |

Round-trip shapes, all **correct**:

| shape | result |
|---|---|
| payload-less variant nested in a payloaded variant, extracted via `rt_enum_payload` | matches fresh disc |
| payload-less variant read from a struct field | matches fresh disc |
| payload-less variant held in a local `var`, reassigned | matches fresh disc |
| payload-less variant bound out of a **multi-field** variant by `match ... case BinOp(dest, op, l, r)` | matches fresh disc |

## REFUTED: the payload-less / ASLR claim

A prior lane reported that `rt_enum_discriminant` returns *unstable, pointer-shaped
garbage for payload-less variants*, such that `MirBinOp.Add` would compare equal to
`MirBinOp.Eq`. **This was tested and does not reproduce.** Payload-less discriminants
are stable across processes, distinct per variant, and correct in all four access
shapes above — including the exact shape used at
`src/compiler/70.backend/backend/cranelift_gemm_fusion.spl:116-125`. Do not re-hunt it.

The real trap is the enum_id blindness documented above, which produces a *similar-looking*
symptom (`Add` compares equal to `Add`) but across enum *families*, not within one.

## Site audit

~230 `rt_enum_discriminant(` call sites in `src/**/*.spl` (excluding `extern fn`
declarations, LLVM `declare` emission, and comments). 13 enum families appear as literal
reference operands. A scan for any single expression comparing discriminants of two
*different* families returned **zero hits** — every comparison in the tree is
within one family, where the hash is a correct discriminator.

**No code fix is warranted.** Adding defensive `rt_enum_id` checks would be an
unverifiable blanket rewrite: no positive control can be built that goes red on revert
for a bug that cannot be triggered.

## Related: the separate `-1` failure mode (already filed)

`rt_enum_discriminant` returns `-1` for any value that is not a
`HeapObjectType::Enum`. There is an existing, independently-filed defect where enum
values retrieved out of a `Dict` by bracket index lose their Enum-ness and read back as
`-1`, so `case`-gates silently never fire:
`doc/08_tracking/bug/symbolkind_enum_match_fails_cross_module_discriminant_minus_one_2026-07-29.md`
(trigger is dict retrieval, **not** payload-less-ness — that doc's own 2026-07-30 update
retracts the original "cross-module" framing). See also
`doc/08_tracking/bug/interpreter_cross_module_enum_discriminant_3_compares_false_2026-08-04.md`
and `doc/08_tracking/bug/simple_core_discriminant_equality_uses_tagged_value_compare_2026-07-13.md`.

Note that `-1` is a *stable* wrong answer, and it collides with nothing in the hash
space, so it is easier to notice than the name-collision described above. Neither mode
is caused by a variant lacking a payload.

## Correct usage

- Prefer `match` — it is the verified-safe construct and is what the codegen lowers to
  a paired `rt_enum_id` + `rt_enum_discriminant` test
  (`src/compiler_rust/compiler/src/codegen/instr/pattern.rs:87-88`).
- If `rt_enum_discriminant` must be used on a value whose enum family is not statically
  pinned, pair it with `rt_enum_id`.
- Never build a name→discriminant table and compare across families.

## Suggested hardening

Fold the enum id into the hash (`hash_variant_discriminant(enum_name, variant_name)`),
or make `rt_enum_check_discriminant` take and verify an `enum_id`. Either is an ABI
change across the Rust runtime, the Cranelift/LLVM backends, and the `.spl` backends.

## Unmeasured lanes

- **Native/AOT:** UNMEASURED. `bin/simple native-build` failed with
  `native-build worker exited with code 1` (pre-existing, unrelated to this probe);
  the machine was also contended by concurrent sessions holding the toolchain.
- **Pure-Simple self-hosted binary:** UNMEASURED. `bin/simple` currently resolves to the
  Rust bootstrap **seed** (it prints the seed warning on every run). Redeploying the
  self-hosted binary was out of scope for this lane.
