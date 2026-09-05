# Stage2 native-build: `has_paren_idx` undeclared global in predicate_parser.spl

- Status: FIXED
- Found: 2026-08-08, during the `stage3_vacuous_binary_is_enum_discriminant_garbage_not_a_link_failure_2026-08-08.md` wildcard-arm bisection (side-finding, unrelated to that bug's original symptom)
- Fixed: 2026-08-09
- File: `src/compiler/00.common/predicate_parser.spl`

## Symptom

Scoping a native-build to `--source src/compiler/00.common` reached LLVM
codegen and failed with:

```
llvm codegen: semantic: llvm global load referenced undeclared symbol 'has_paren_idx'
```

Repro (stage2 binary from `/home/ormastes/dev/simple-s3rv2/build/cyc/RV2/stage2-simple`,
built from origin/main @ `be775aa04fdbaa6b9548c74aec17413543698f12`, 2026-08-08):

```
stage2-simple native-build --backend llvm --mode dynload \
  --entry <trivial main.spl> \
  --source src/compiler/00.common --output out
```

## Root cause

`src/compiler/00.common/predicate_parser.spl`, function
`parse_signature_pattern`, around line 245 (pre-fix):

```
val paren_idx = rest.index_of("(")
if not has_paren_idx:
    return SignaturePattern(return_type: return_type, qualified_name: rest,
                            args: ArgPatterns.Any)

val qualified_name = rest[:paren_idx_value]
val args_str = rest[paren_idx_value + 1:]
```

`text.index_of` returns `i64` (not an `Option`/presence-flag pair), and the
declared local is `paren_idx`. The code instead references `has_paren_idx`
and `paren_idx_value` — neither was ever declared anywhere in the file or
module. This is a plain source-level typo/copy-paste bug in the `.spl` file
itself, not a codegen defect: `has_paren_idx` and `paren_idx_value` are
genuinely undefined identifiers, and LLVM codegen correctly refused to emit a
load for an undeclared global (it apparently falls back to treating an
unresolved bare identifier as an implicit-global reference rather than a
hard frontend error).

**Why this was invisible until now:** the interpreter/tree-walk path (used
by `bin/simple test` and most everyday runs) treats an unresolved variable
reference as silently permissive in some paths (see
`reference_silent_interpreted_fallback_hir_unknown_variable.md` and
`reference_unresolved_use_is_only_a_warning_so_delete_verification_is_fail_open.md`
in memory) — so this bug only surfaces when the LLVM/native codegen path
actually tries to compile `parse_signature_pattern` to real symbol
references, which requires scoping a native-build to reach this specific
module. It was not the cause of the original stage3 vacuous-binary bug being
bisected; it's an unrelated defect found along the way.

## Fix

Use the actually-declared `paren_idx` (and its natural "not found" sentinel,
`< 0`, since `index_of` returns `-1` on no match, not an `Option`):

```
val paren_idx = rest.index_of("(")
if paren_idx < 0:
    return SignaturePattern(return_type: return_type, qualified_name: rest,
                            args: ArgPatterns.Any)

val qualified_name = rest[:paren_idx]
val args_str = rest[paren_idx + 1:]
```

## Regression evidence

1. Reverted the file to the pre-fix (origin `HEAD`) content and re-ran the
   exact repro command above against the same stage2 binary — reproduced the
   identical error twice:
   ```
   llvm codegen: semantic: llvm global load referenced undeclared symbol `has_paren_idx`
   ```
2. Restored the fix and re-ran — native-build of `src/compiler/00.common`
   completed cleanly (`Build complete: 66 compiled, 0 cached, 0 failed`), no
   `has_paren_idx`/undeclared-symbol errors in output.
3. Added a narrow, fast (~10s) regression check scoped to just this module:
   `scripts/check/check-predicate-parser-native-build.shs <stage2-binary>`.
   It native-builds a trivial entry against `src/compiler/00.common` only and
   fails if any "llvm global load referenced undeclared symbol" appears in
   the build log. Confirmed PASS against the fixed source.

## Follow-up (not done here, out of scope)

The interpreter's silent tolerance of unresolved-variable references (rather
than a hard frontend name-resolution error) is a broader fail-open gap — this
exact bug should have been caught by name resolution at parse/semantic-check
time regardless of backend. That's tracked separately in the memory entries
referenced above; not re-litigated in this bug doc.
