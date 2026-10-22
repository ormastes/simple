# Typed dictionary tuple binders lose nominal types during bootstrap

Canonical ID: `dict_nominal_tuple_binders_any_bootstrap_2026_10_21`
Status: open; typed-local bootstrap workaround, root inference repair pending.
Bug DB reconciliation: pending a qualified self-hosted DB command; the Rust
seed is used only for bootstrap diagnostics and cannot provide that admission.

## Producer and failure

Source `0bfa8039acd`, Windows LLVM Phase 2, Rust bootstrap seed SHA-256
`32014B3401E3CB76AEC44ACB475A22F2385FEFCD1D19AB71049E52D633356825`.
Producer path in the frozen parent tree:
`.simple/storage/build/bootstrap/stage3/x86_64-pc-windows-msvc/stage2-runtime-authority/simple.exe`.
Canonical `stage2-native-build.log` records 1431 compiled and five failed
modules, including these three dictionary tuple-binder failures:

- `enum_pattern_physical_v1.spl`: `EnumPatternPhysicalCheckerV1.validate`,
  erased `site.instruction_index`.
- `enum_semantic_identity_v1.spl`: `enum_semantic_declaration_identity_v1`,
  erased `key.id`.
- `enum_semantic_validation_v1.spl`: `EnumPhysicalValidatorV1.preflight`,
  erased `declaration.symbol`.

Rust `TypeRegistry::get_iterable_element` omits `HirType::Dict`. Tuple-for
lowering consequently registers both binders as `ANY`. Receiver-blind field
lookup can conceal this when a field has only one candidate layout; with
conflicting nominal layouts it correctly rejects an unsafe guessed access.
Pure-Simple tuple-for HIR lowering also currently records nil binder types.

## Scoped workaround and retirement

Keep dictionary iteration order, keys, values, work charging, errors and
validation unchanged. Bind explicit nominal typed locals immediately inside
the affected loops, including the next declarations loop in preflight. This
restores existing declared dictionary K/V types without inferring layouts by
field names. Each block carries this canonical ID and the recovery revision.
The workaround commit is the Git commit introducing these linked blocks.

Root-fix owner: compiler dictionary-iterable/tuple-binder typing (deferred by
the merge owner to preserve the successful canonical objects). Remove only
after a rebuilt admitted producer compiles and executes the original fixture
with conflicting nominal layouts and the original enum modules without the
typed locals. Do not treat this source workaround as an inference fix.

## Diagnostic evidence

Private evidence: `build/session/enum-dict-any/`. The initial single-layout
control compiled and ran to 31, exposing why that control alone was weak.
Adding conflicting `id`, `symbol`, and `instruction_index` layouts reproduces
the exact `ANY.id` failure. The retained original fixture is
`test/fixtures/native_dict_nominal_loop/main.spl`; positive typed-local and
affected-module verification results are recorded after execution.
No canonical source/cache writer or successful object was modified.

## Verified workaround evidence

Workaround commit: `52a094ba279` (original forms recoverable from
`0bfa8039acd`). One scoped source repair was verified; no inference-owner or
producer change was made. The original conflicting-layout fixture remains
intentionally failing under this seed, with exit 1 and `ANY.id` diagnostic in
`ambiguous-original/build.log` and `result.env`.

The typed control uses exactly the same conflicting layouts. Its fresh
`typed-positive/` build compiled one module with zero failures, linked, and
executed `PASS: dictionary nominal tuple binders = 31` with exit zero.
Executable SHA-256:
`3ACD1A3E7755139D60D641B3BA0BE6EB6499B4BC7B0CBB18591F6281BD4EAF7C`.

The exact Rust seed does not implement `--emit-object`; use its supported
archive surface rather than treating a Pure-Simple-only flag as implemented:

```sh
"$seed" native-build --backend llvm --runtime-bundle core-c-bootstrap \
  --source "$entry" --entry "$entry" --entry-closure --threads 1 \
  --cache-dir "$private_module/cache" --emit-archive --mode one-binary \
  --target x86_64-pc-windows-msvc --runtime-path "$(dirname "$seed")" \
  -o "$private_module/module.lib"
```

Each module had an independent fresh cache. The commands, per-module logs and
exit statuses are retained in `build/session/enum-dict-any/modules.sh` and
`modules/<module>/`; runtime object cache, HOME and temporary paths were also
private. Results (all zero failures, zero cached; archive byte sizes):

| Entry | Compiled closure modules | Seconds | Bytes | Defined symbol confirmed |
|---|---:|---:|---:|---|
| `enum_pattern_physical_v1` | 128 | 31.5 | 2533708 | `EnumPatternPhysicalCheckerV1.validate` |
| `enum_semantic_identity_v1` | 128 | 29.3 | 2470670 | `enum_semantic_declaration_identity_v1` |
| `enum_semantic_validation_v1` | 134 | 32.9 | 2819468 | `EnumPhysicalValidatorV1.preflight` |

Archive SHA-256 values, in table order:

- `FC76E5F98C4DA8F076DB5C2B77EACB076E912095E3D52FE8B92368215662DF18`
- `E5EC0C2058307751FE47E5C0101573BC63F9D001AE119DFE075AA110C4DC6FE9`
- `49D21B821122B841C014361AB3BA08B7868A111CDE27E66BB76BD621E1D04344`

LLVM 23.1.1 `llvm-nm --defined-only` confirmed the actual failing function
symbols in these archives. Archive construction does not prove the full
compiler executable links, nor qualify Phase 2/3 or general SPipe execution.
