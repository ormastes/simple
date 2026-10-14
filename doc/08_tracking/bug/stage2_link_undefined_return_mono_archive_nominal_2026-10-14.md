# Site 18: Stage 2 does not LINK on `release_phase3` — undefined `_return` from `MonomorphizationPass.ensure_archive_nominal_table_v2`

## Status: ROOT CAUSE FIXED (Rust seed parser, PR #3484); source workaround PR #3483; 2026-10-14

## Symptom

Stage 1→2 bootstrap with the canonical candidate invocation:

```
sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --backend=llvm --mode=dynload --full-bootstrap \
  --stop-after-stage2 --no-mcp --jobs=4
```

fails at the Stage-2 native link on macOS aarch64 (isolated worktree at
`release_phase3` tip, macOS 26.5, Apple Clang 17 linker, Homebrew LLVM 23
provider):

```
warning: unresolved call `return` in function
  `compiler__mono__monomorphize_integration__MonomorphizationPass.ensure_archive_nominal_table_v2`
Undefined symbols for architecture arm64:
  "_return", referenced from:
      _compiler__mono__monomorphize_integration__MonomorphizationPass.ensure_archive_nominal_table_v2 in libspl_objects.a(mod_420.o)
clang++: error: linker command failed with exit code 1
error: strict bootstrap stage2 failed (exit 1); refusing seed fallback
```

Retained log:
`/private/tmp/simple-rp3-boot/.simple/storage/build/bootstrap/logs/aarch64-apple-darwin/stage2-native-build.log`

Same failure class as
`stage2_link_undefined_module_surfaces_promote_reason_sffi_enum_discriminant_2026-09-13.md`
(site 17): a dangling pure-Simple symbol reference, not a runtime extern gap.

## Root cause (minimal repro)

The **Rust seed parser** mis-lowers a single-line `else: return <expr>` when
it follows a single-line `if` whose branch is an expression statement. The
else body is compiled as an expression — a global load of an undeclared
symbol literally named `return` — instead of a return statement.

Minimal repro (compiles wrong under the seed, ~2s with
`simple native-build --source src --entry <file>`):

```spl
fn f(flag: bool) -> bool:
    if flag: g()
    else: return false
    true
```

Block-form `else:` parses and lowers correctly:

```spl
    else:
        return false
```

The trigger site in product source:
`src/compiler/40.mono/monomorphize_integration.spl` —
`MonomorphizationPass.ensure_archive_nominal_table_v2`, the
`else: return false` arm of the archive-row loop (line ~754 at `fb78c0c652b`).
PR #3479 (`work/phase3-mono-index-guard-20261014`) does **not** fix it
(measured: identical link failure with that branch applied).

## Landed workaround

Branch `fix/mono-inline-else-return-stage2-link-20261014` converts the single
offending `else: return false` to block form. Only one site of this shape
exists in the compiled tree (exactly one `unresolved call 'return'` warning
across the whole stage2 build). This unblocks the stage2 link; it does NOT
fix the seed parser.

## Root cause fix (landed)

PR #3484 (`fix/seed-parser-inline-else-return-20261014`): the inline
expression-if path in `parse_if` and the inline elif/else bodies in
`finish_inline_statement_if` parsed their body with `parse_expression` /
`parse_expression_or_assignment`, treating `return` as an identifier;
`parse_if_expr` already had the Return/Break/Continue guard. The fix applies
the same guard (DoBlock wrap) at the three missing sites, with parser
regression tests. Verified: the minimal repro compiles and runs correctly
under the rebuilt seed; the full simple-parser suite passes (one
error_recovery failure pre-exists on unmodified release_phase3).

PR #3483's block-form source workaround remains valid for the CURRENT
admitted seed and can be reverted once a seed built from PR #3484 is
admitted.

Gate reminder (from `doc/03_plan/phase3_bootstrap_remaining_2026-10-13.md`):
Phase 3 and native Hello World must pass before landing compiler changes;
land fixes one at a time after review.
