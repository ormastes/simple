# ROOT: `Option<T>` None promoted to Some because None-ness is decided from STATIC nil provenance

**Date:** 2026-09-14
**Status:** FIXED at the lowering (unverified by execution — see Evidence)
**Severity:** P1 — silent wrong answer that becomes `EXC_BAD_ACCESS` at the first field read
**Component:** `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`
(`ensure_option_handle`), plus a secondary twin divergence in
`src/runtime/simple_core/`

## The class this closes

Under the STAGED native ABI — a compiler compiled by a pure-Simple compiler,
i.e. Stage 2/3 candidates — an `Option<T>` whose value is None arrives such that
`.?` / `is_some` read PRESENT while `unwrap()` yields nil, so every
`if x.? … x.unwrap().field` site faults at a small offset. PR #1001 added the
twelfth `if info == nil: return` guard at
`_MirLowering/module_lowering.spl:455` (`EXC_BAD_ACCESS code=1 address=0x48` at
`record_external_layout_reference + 204`); `mir_struct_symbol_name` in the same
file documents the same hazard; the 2026-07-18 baremetal family
(`baremetal_option_field_unwrap_faults_class_2026-07-18.md`) is five more sites
of the identical mechanical rewrite. Those are all per-site symptom management.

## Root

`ensure_option_handle` promotes a typed Optional value to the canonical
enum-id-1 handle. It chose the discriminant like this:

```
val disc = if self.nil_locals.has(local.id): 1 else: 0
```

`nil_locals` is a **compile-time** marker set, populated syntactically and
propagated by assignment (`mir_lowering_stmts.spl:712,1254,1547,1776`). So the
promotion answers "is this None?" with "was this local *written as* `nil` in the
source?".

That is only sound when absence is statically knowable. It is not for a value
whose absence is decided at RUNTIME:

- a `Dict` bracket/`get` read that missed,
- a nilable returned from another function and relayed,
- a variable assigned nil on some other branch.

None of those are in `nil_locals`, so each was promoted with **disc = 0 (Some)
around a nil payload word**. `.?`/`is_some` then answer PRESENT (the handle is a
well-formed Some), `unwrap()` returns the nil payload, and `.field` dereferences
`nil + offset` — `address=0x48` is field offset 0x48 of the struct that was
never there.

`get_symbol_raw` (`20.hir/hir_symbol_table_methods.spl:242`) is exactly this
shape and is the crashing call site:

```
if self.symbols.has(raw):
    return self.symbols[raw]      # NOT in nil_locals -> promoted as Some
nil                               # in nil_locals -> promoted as None
```

Its two sibling helpers in the same file already carry docstrings describing the
symptom ("`.?` reports Some while `unwrap()` yields a null payload") and route
around it with scalar returns — further evidence the defect is one producer, not
many consumers.

### Fix

For a **boxed** payload (text, array, slice, dict, tuple, struct, class, dyn)
the raw word 3 is unambiguously the nil sentinel — no live handle of those kinds
has that bit pattern — so the discriminant is now selected from the payload word
at runtime: `disc = (payload == 3)`, i.e. None=1 exactly when the payload is
nil. The handle layout is unchanged (enum_id 1, Some=0 / None=1), so this is
ABI-compatible with every existing consumer on every lane.

For a **scalar** payload (`i64?`, `bool?`, `f64?`, `char?`) the static path is
kept verbatim: 3 is both a legal `i64` payload and the nil sentinel, so the
payload word cannot decide it and provenance remains the only available answer.
`Ptr`/`Ref` are excluded for the same reason — a raw address space does not
reserve the sentinel. The predicate is `option_payload_is_boxed`.

### Secondary: simple-core twin divergence (not the root, fixed here anyway)

Both reference runtimes accept the legacy HASHED None discriminant alongside the
positional one — `runtime_native.c:4716` (`discriminant == 1 || discriminant ==
RT_DISC_NONE`) and `compiler_rust/runtime/src/value/objects.rs:552`. The
pure-Simple twins accepted only the positional `1`:

- `src/runtime/simple_core/core_values.spl:130` (`rt_is_none`)
- `src/runtime/simple_core/core_string.spl:1010` (`rt_is_present`, i.e. `.?`)

while `rt_unwrap_or_trap` twelve lines below `rt_is_none` already knew the
hashed form — the same "presence says yes, unwrap says no" split, in the twin
that a staged native binary links. Both are brought into agreement with the C
and Rust twins. This is parity hygiene; it is **not** the root, because nothing
under `src/compiler/` emits the hashed discriminant today.

## Evidence

- Interpreter (the oracle) is correct for every variant: 11/11 pass,
  `test/01_unit/compiler/option_none_runtime_discriminant_spec.spl`.
- Seed native lane (`check-native-interp-differential.shs` on the pinned row):
  `PASS — 1 spec(s) compared, 0 divergent`. The seed's native pipeline links
  `runtime_native.c` and does not run this lowering, so **the harness row is
  seed-clean both before and after** — it is a regression fence, not the proof.
- The Stage 2 candidate available on this host
  (`…/agent-ac40c7a12fcd24543/.simple/storage/build/bootstrap/stage2/aarch64-apple-darwin/simple`)
  **rc-139s in `native_compile` on a two-function scalar-only probe**, before
  reaching any Option code, so it could not be used to reproduce or to verify.
  That is the #1001 crash class itself and is F75's chain to repair.
- **Therefore the fix is unverified by execution.** The proof is the next Stage 2
  rebuild: `build/f78_status.txt` records the landing so F75's chain picks it up.

### A trap this spec hit, recorded so the next author does not

An earlier draft wrote `expect(o.?).to_equal(false)`. That form failed **8 of 10
examples natively, including the Some cases and the scalar cases** — a bare
optional in argument position has its own defect
(`bare_optional_in_condition_position_wrong_branch_2026-08-01.md`) and swamps
the signal. Presence must be read through `if x.?:` in a helper returning a
plain `bool`, which is also what product code writes.

## Removable debt (do NOT remove yet)

The per-site `if info == nil: return` / `if info != nil` guards are cheap and
defensive and stay. They become removable once a Stage 2 built with this fix is
green: `_MirLowering/module_lowering.spl:455` (PR #1001) and `:508`
(`mir_struct_symbol_name`), plus the `match`-based rewrites listed in
`baremetal_option_field_unwrap_faults_class_2026-07-18.md`. Removing one is a
separate, individually-verified change.

## Files

- `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` —
  `option_payload_is_boxed`, `ensure_option_handle` runtime discriminant
- `src/runtime/simple_core/core_values.spl` — `rt_is_none` hashed-None parity
- `src/runtime/simple_core/core_string.spl` — `rt_is_present` hashed-None parity
- `test/01_unit/compiler/option_none_runtime_discriminant_spec.spl` — 11 examples
- `config/check/native_interp_differential_pinned.txt` — always-compared rows
- `scripts/check/check-native-interp-differential.shs` — pinned-row curation

## Pre-push: test-tree divergence delta step-over (recorded)

`check-test-tree-divergence.shs` is RED on `origin/main` and was already red
before this range. The scoped-delta escape was used, mechanically, not by
judgement:

```
check-test-tree-divergence-delta.shs origin/main HEAD
  base verdict: FAIL — 3945 diverged vs 965 baselined (3083 new,
                103 fixed-but-still-baselined); 32 mirror-only
                (31 unallowlisted, 0 stale-allowlist)
  PASS — 3217 pre-existing offender(s), 0 introduced by this range   (exit 0)
```

Pre-existing offender list saved by the helper at
`$TMPDIR/test_tree_divergence_preexisting.txt` (3217 entries), recorded here as
the escape requires. The only mirror-tree path this range touches is
`test/01_unit/compiler/option_none_runtime_discriminant_spec.spl`, a new spec
with no twin on either side; the delta guard's own offender-list diff — not
that observation — is the authority, and it reports zero introduced.
