# Enum discriminant convention split: hashed (seed) vs positional (pure-Simple)

- **Filed:** 2026-08-08
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
  is established at *source* level and confirmed on the one stage artifact
  available; artifact-level coverage of the seed-emitted leg is INCOMPLETE (see
  Reachability § limits).
- **Severity:** low today / high the day the two link envelopes are mixed
- **Area:** `50.mir` try-lowering, `codegen/instr/result.rs`, both runtimes, stage4 link envelope

## Summary

This codebase carries **two mutually incompatible enum-discriminant
conventions**, one per toolchain. Each toolchain is internally consistent —
its codegen and the runtime it links agree — so nothing is broken today. But
the two are only kept apart by the *link envelope*, not by any type, ABI
version tag, or assertion. Nothing detects a mix.

| | discriminant for `Result.Err` | `Option.None` |
|---|---|---|
| **Rust seed** (codegen + Rust runtime) | `hash_variant_discriminant("Err")` — Rust `DefaultHasher`, `& 0xFFFFFFFF` | `hash_variant_discriminant("None")` |
| **Pure-Simple** (codegen + C runtime) | positional index `1` | positional index `1` (Some=0) |

## What each side actually emits

**Rust seed — HASHED, on both construction and test.**
- Construction: `src/compiler_rust/compiler/src/codegen/instr/result.rs:102`
  `create_enum_value(ctx, builder, dest, 0, variant_disc("Err"), Some(value))`.
  `variant_disc` (`result.rs:13`) is `DefaultHasher(name) & 0xFFFFFFFF`.
- Test (`?`): `result.rs:53-58` — `rt_enum_discriminant` compared against
  `variant_disc("Err")`.
- Its runtime agrees: `src/compiler_rust/runtime/src/value/objects.rs:262,266`
  (`rt_option_none`/`rt_option_some`), `:340` (`rt_is_none`), and
  `value/collections.rs:654` (`rt_array_at`) are all hashed. **No positional
  constant anywhere in the Rust runtime.**
- Bytecode emitter also bakes hashed u32s:
  `codegen/bytecode/compiler.rs:175,499`.

**Pure-Simple — POSITIONAL, on both construction and test.**
- Construction: `lower_enum_construct_named` -> `rt_enum_new` with
  `enum_variant_disc`; Result registers `Ok=0, Err=1`
  (`50.mir/_MirLoweringExpr/switch_operators_calls.spl:4036`).
- Test (`?`): `lower_try_expr`, same file — `err_key = emit_const_int(1)`
  compared against `rt_enum_discriminant`.
- Its runtime agrees: `src/runtime/runtime_native.c` is uniformly positional —
  `rt_array_at` `rt_enum_new(1,1,nil)` / `rt_enum_new(1,0,elem)` (:6379-6387),
  `rt_is_none` `rt_enum_id==1 && rt_enum_discriminant==1` (:3694),
  `rt_core_format_enum` Result id 0 with `disc==1 => Err` (:2777).
  **No hashed constant anywhere in the C runtime.**

Neither `rt_enum_new` validates or canonicalises the discriminant — both store
the caller's `u32` verbatim — so a mix is silent, not a crash.

## Reachability in the bootstrap — no live cross-over found

Runtime provenance of the actual artifacts, via **`.rodata` canaries** (symbol
tables are useless here: `bootstrap/stage3/simple` is `stripped` and `nm`
returns nothing at all, so any symbol-absence test on it fails open):

- C-runtime canary: the string literal `"Result::Err("`
  (`runtime_native.c:2781`).
- Rust-runtime canary: Rust panic-location strings `runtime/src/value…`.
  **Positive control:** `bin/simple`, a known Rust-runtime binary, yields 78
  hits — so a `0` is a real absence, not a stripped-away symbol.

| binary | `Result::Err(` | `runtime/src/value` | runtime |
|---|---|---|---|
| `bin/simple` (currently a Rust **seed** build) | 0 | 78 | Rust / hashed |
| `bootstrap/stage3/simple` (stripped) | 1 | 0 | C / positional, **single convention** |

No duplicate-`rt_enum_new` mixed link in that artifact.

**Limit of this measurement:** `bootstrap/stage1/`, `stage2/`, `stage3/simple`
are **byte-identical** (md5 `2244f18ce2e694fb7ca395e9916404c3`, same mtime) —
one binary of undetermined provenance, almost certainly copies rather than a
three-stage fixpoint. So the table says nothing about the stage2 leg
specifically, and the one combination that *would* be live — **seed-emitted
code (hashed) linked against the C runtime (positional)**, which
`SIMPLE_NATIVE_BUILD_RUST=1` on stage2 makes conceivable — has **not** been
observed and has **not** been excluded on an artifact. Re-check it the moment
`native-build` is usable again (see Oracle notes).

The envelopes are **disjoint by source-level construction**:
- The seed's native linker takes `libsimple_runtime.a` (Rust) —
  `compiler/src/linker/native_binary/linker.rs:130`.
- The pure-Simple stage4 linker **explicitly rejects** `libsimple_runtime.a`
  as a "forbidden aggregate path" —
  `70.backend/backend/stage4_symbol_closure.spl:739-741` — and links the C
  runtime objects from `runtime_compiler.spl:284`.

No serialized carrier crosses the two, either:
- Enum values are heap pointers, interned in a **per-process** table
  (`runtime_native.c:6285 rt_enum_intern_table`). They cannot survive a
  process boundary, so no `.sdn`, module cache, or test DB can carry one.
- The one artifact that *does* serialize a discriminant is the seed's
  **bytecode** (`compiler.rs:175,499`, hashed). It is written and read only by
  the seed; the pure-Simple VM lane is `70.backend/svmg_lowering.spl`, an
  unrelated format. No pure-Simple consumer.

**Conclusion: latent.** A cross-over needs a single link that mixes C-runtime
and Rust-runtime `rt_enum_*`. That is currently forbidden — but only by one
string check in one `.spl` validator, and the seed linker passes
`--allow-multiple-definition` (`linker.rs:145`), so a duplicate-symbol mix
would link silently rather than error.

## Does it explain any open Stage-3 blocker? NO

`unresolved type: ByteOrder` in `cache_validator.spl` and the `Effect` facade
collision in `50.mir/__init__.spl` are frontend name-resolution diagnostics. A
discriminant mismatch can only produce a wrong branch or a garbage payload at
run time; it can never produce an unresolved-type error. Mechanism mismatch —
no connection, not forced.

## Oracle notes (why the usual harnesses cannot see this)

- **The interpreter is structurally blind by construction**, not by accident:
  `interpreter_extern/enum_sffi.rs:26` hashes `variant` from the live
  `Value::Enum { variant }` *name* at read time, so construction and test can
  never disagree there. `bin/simple test` cannot detect this class.
- Reproduce with this probe (kept inline; the scratchpad copy is ephemeral):

```simple
fn get(i: i64) -> Result<i64, text>:
    if i < 0:
        return Err("neg")
    Ok(i * 2)

fn use_it(i: i64) -> Result<i64, text>:
    val v = get(i)?
    Ok(v + 1)

fn main():
    match use_it(5):
        case Ok(v):
            print("ok5=" + v.to_text())
        case Err(e):
            print("err5=" + e)
    match use_it(-1):
        case Ok(v):
            print("okneg=" + v.to_text())
        case Err(e):
            print("errneg=" + e)
    val xs = [10, 20]
    print("at0=" + (xs.at(0) ?? 999).to_text())
    print("at9=" + (xs.at(9) ?? 999).to_text())
```

- Seed interpreter and seed JIT both handled `?`
  correctly (`ok5=11`, `errneg=neg`) — as expected, since each is
  self-consistent.
- The **native** leg of the probe could NOT be run: `native-build` fails in the
  current working copy on an unrelated in-flight stdlib break — `ambiguous
  package export MailboxConfig in src/lib/nogc_async_mut/__init__.spl
  (mailbox.spl vs mailbox_actor.spl)`. Recorded rather than worked around; it
  is another session's lane.

## Secondary observations (not fixed here)

- `variant_disc` uses Rust's `DefaultHasher` (SipHash-1-3, zero keys). It is
  deterministic within a build but **not guaranteed stable across Rust
  releases**. Any seed rebuilt on a different rustc that changed `DefaultHasher`
  would silently change every discriminant it emits. The Rust runtime and the
  seed codegen both compute it, so they would move together *only if built
  together*; a stale `libsimple_runtime.a` plus a fresh compiler would not.
- `xs.at(9) ?? 999` printed `nil` (not `999`) under the seed JIT while the
  interpreter printed `999`. That is a `??`-lowering defect, orthogonal to this
  finding and not investigated here.
- The `lower_try_expr` docstring asserts `rt_is_none` "tests a legacy HASHED
  constant". That is **true of the Rust runtime only**; the C runtime that the
  pure-Simple lane actually links is positional (`runtime_native.c:3694`). The
  docstring should name which runtime it means.

## Recommended fix (converge, or fence)

Converging the representations is the right end state, but it is a
cross-toolchain ABI change and must not be done as a drive-by while stage3 is
blocked and the working copy carries ~23 in-flight edits. The minimum
non-negotiable guardrail, in priority order:

1. **Fence it.** Make the pure-Simple stage4 link check reject *any* archive
   exporting `hash_variant_discriminant`, not just the two names it string-
   matches today; and make the seed's link fail (not `--allow-multiple-
   definition` past) on a duplicate `rt_enum_new`.
2. **Converge on positional.** It is already the convention of the C runtime,
   the pure-Simple codegen, and the self-hosted product; only the seed and the
   Rust runtime are hashed, and the seed is bootstrap-only. Changing
   `variant_disc` in `result.rs` + `hash_variant_discriminant` call sites in
   `runtime/src/value/objects.rs` and `collections.rs` to the positional index
   is the smaller edit and removes the `DefaultHasher`-stability exposure too.
   Both must land in the SAME change — a half-migrated seed is a live wrong-
   branch bug where today there is none.

## Related

- `ff3a00cb093` — try-operator blast-radius audit that reported this divergence.
- Payload-less-enum `rt_enum_discriminant` instability is a **separate**
  primitive defect owned by another lane (agent `a8b04238e9b9afc61`). `Result`
  variants carry payloads, so this finding does not depend on that primitive
  being sound.
