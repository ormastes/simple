> **RESOLVED 2026-07-20 — root-fixed.** The driver's native-build MIR path
> (`driver_pipeline.spl`, `direct_lowering`) built its `MirLowering` from a
> **hand-duplicated copy** of the canonical `MirLowering.new_for_target`
> constructor that had drifted out of sync — it **omitted 8 fields**
> (`struct_field_has_default`, `struct_field_default_expr`, `struct_field_hir_type`,
> `runtime_value_locals`, `option_value_locals`, `nil_locals`,
> `enum_runtime_id_index`, `enum_runtime_id_names`). The seed interpreter
> **silently nil-fills** any struct-init field omitted from a constructor call
> (it does not error at construction — see the documented landmine in
> `mir_lowering_types.spl` for `global_static_ids`), so those 8 fields read back
> as `nil`, and the first `.has(...)`/index on one crashed MIR lowering with
> `method has not found on type nil`. It reproduced on **every** struct
> construction (construct-only, i64 or f64 field) but ONLY on native-build,
> because `run`/`test` use the Rust HIR/MIR lowering, not this pure-Simple path.
>
> Fix: collapse both driver copies into the canonical `new_for_target` call.
> `check-bootstrap-portability.shs` rejects any new direct driver constructor,
> requires both active driver paths to use `new_for_target`, and pins the enum
> runtime-ID maps in that canonical owner. Behavioral regression guard:
> `test/03_system/native/struct_construct_native.spl`. This also unblocks the
> struct-field-f64 case of the container-f64 heap-box fix on native-build (see
> seed_f64_array_element_precision_mask).

---

# `native-build --entry` BUILDFAILs on any local struct construction — `method has not found on nil`

- **id:** native_build_entry_struct_construction_buildfail_2026-07-20
- **status:** resolved 2026-07-20 (root-fixed — driver_pipeline.spl duplicated-constructor drift; see top banner)
- **severity:** high (a first-class construct — defining and constructing a
  struct — cannot be single-file native-built at all)
- **component:** compiler — `native-build --entry` single-file mode; the
  interpreted pure-Simple compiler's MIR/struct lowering (`method has not found
  on nil` is an ICE surfaced as a semantic diagnostic, not a user type error)
- **found on:** pristine origin tip (`27ab2ddc498`, still reproduces at
  `935427442ac`); seed = `src/compiler_rust/target/release/simple` built at
  origin tip. **Reproduces on a clean origin-tip worktree** — not a local-branch
  or working-copy defect.

## Symptom

Any program that defines and constructs a struct fails to native-build:

```simple
struct P:
    x: i64
fn main() -> i64:
    val p = P(x: 7)
    return 30
```

```
$ simple native-build --entry n_sctor.spl -o /tmp/out --clean
error: semantic: method `has` not found on type `nil` (receiver value: nil)
```

## Scope (characterized by build matrix on clean origin)

- **Construct-only** (`val p = P(x: 7); return 30`) → BUILDFAIL.
- **Construct + field read** (`return p.x`) → BUILDFAIL (same error).
- **Construct + field compare** (`if p.x == 7: ...`) → BUILDFAIL (same error).
- **i64 field and f64 field** → both BUILDFAIL identically, so the defect is
  **not float-related**.
- **Contrast — same `--entry` mode, same seed, all build + run fine:** array
  element (`[0.1,0.2,0.3][0]`), dict value/key, scalar f64, for-in, int/string
  arrays, `print`. So `native-build --entry` is broadly functional; struct
  construction specifically is broken.

The error is a compiler internal error (`method has not found` on a `nil`
receiver) during the interpreted compiler's lowering — the struct parses and is
semantically recognized, then a lowering step dereferences a `nil` Option-like
value. Full-project bootstrap builds (which compile the struct-heavy compiler
itself) are **not** exercised by this repro and are out of scope for this entry.

## Impact / cross-refs

- Blocks the **struct-field** case of the container-f64 heap-box fix on
  native-build: a struct with an `f64` field cannot be built to verify the
  round-trip. That float path IS verified lossless on the interp/JIT path
  (`aa7ae5506c6`) and the native box/unbox arms are proven correct for
  array/dict/scalar/for-in; only this struct-construction BUILDFAIL blocks the
  struct variant. See
  [seed_f64_array_element_precision_mask_2026-07-19](seed_f64_array_element_precision_mask_2026-07-19.md).
- Sibling native-build Option defect (also blocks a container-f64 case):
  [hosted_native_option_try_unwrap_payload_leak_2026-07-19](hosted_native_option_try_unwrap_payload_leak_2026-07-19.md).

## Verification

Run `sh scripts/check/check-bootstrap-portability.shs` for the constructor-owner
contract and `test/03_system/native/struct_construct_native.spl` through an
admitted pure-Simple runner for behavior. The static contract is not a
substitute for the native execution probe.
