# `native-build --entry` BUILDFAILs on any local struct construction — `method has not found on nil`

- **id:** native_build_entry_struct_construction_buildfail_2026-07-20
- **status:** open
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

## Next step

Trace the interpreted compiler's struct-construction lowering under
`native-build --entry` to the `nil` receiver of the `.has` call (likely a struct
type/layout lookup returning `nil` in single-file `--entry` mode where the full
pipeline populates it). Add a `native-build --entry` struct-construct probe to
the native smoke matrix once fixed.
