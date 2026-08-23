# Stage 3 self-host aborts: module surface promotion gets nil `friends` / `internal_exports`

- Date: 2026-08-23
- Status: FIXED (source fix landed; needs a full bootstrap to be observed green)
- Severity: blocker — Stage 3 of the bootstrap could not start

## Symptom (VERIFIED, reproduced in an own worktree)

```
[ERROR] phase 2 FAILED (1 recorded error(s))
[ERROR]   Module surface extraction error: module surface promotion failed for src/app/cli/bootstrap_main.spl
[build] parse unknown/967 step 1/6 +27179ms dt=2953ms failed
```

rc=1, not a SIGSEGV. It fails at step 1/6 (parse), on the FIRST source file:
`grep -c promote-done` in the stage-3 log is **0**, so this is systemic, not
specific to `bootstrap_main.spl`.

Reproduced with the stage-2 binary copied out of the bootstrap tree:

```
SIMPLE_BOOTSTRAP=1 SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=1 \
SIMPLE_STAGE3_STREAMING_SURFACES=1 \
  ./s2 native-build src/app/cli/bootstrap_main.spl -o out
```

(The three env vars are the gate `driver_streaming_surface_enabled`,
`src/compiler/80.driver/driver_phase_gates.spl:24-32`. Without them the
streaming-surface path is not taken and the defect does not appear.)

## Root cause (VERIFIED by gdb on the stage-2 binary)

`src/compiler/80.driver/driver_source_pipeline_parsing.spl:327` calls
`module_surface_promote(surface)`, which promotes ~30 retained owners with
`rt_transient_heap_promote`. Breaking on that runtime entry and on
`compiler__hir__hir_lowering__module_surface_registry__module_surface_promote`
showed exactly three calls before the failure:

```
PROMOTE arg=0x1a52a231     # surface.imports   (heap)
PROMOTE arg=0x1a52a2f1     # surface.exports   (heap)
PROMOTE arg=0x3            # surface.friends   -> TAG_SPECIAL|NIL
```

`0x3` is `RT_VALUE_TAG_SPECIAL (0x3)` with payload `RT_VALUE_SPECIAL_NIL (0x0)`
(`src/runtime/runtime_native.c:97-104`). `rt_core_transient_classify`
(`:1884-1926`) returns 0 for a non-heap value, so `rt_transient_heap_promote`
(`:1988`) returns 0 — a false "promotion failed".

Dumping the whole `ModuleSurface` object confirmed that of ~40 fields exactly
**two** were nil, adjacent: `friends` and `internal_exports`. Those are exactly
the two built with `.copy()` at
`src/compiler/20.hir/hir_lowering/module_surface_declarations.spl:392-393` —
and `rt_array_copy` (`runtime_native.c:6930-6932`) returns its argument
unchanged when the source is not an array, so `.copy()` merely PROPAGATED a nil
it did not create.

The nil originates in `parser_module_new`
(`src/compiler/10.frontend/parser_types.spl:674-675`), whose last two
parameters are **trailing defaults**:

```
friends: [text] = [],
internal_exports: [text] = []
```

Both call sites omitted them:
`src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl:224`
(`flat_empty_module`) and
`src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl:1048`.
Breaking on `compiler__frontend__parser_types__parser_module_new` and dumping
the stack argument area showed only **17 stack slots** occupied (params 7..23);
the slots where params 24 and 25 would live held the return address and
saved-register garbage. The two defaulted arguments were **never passed**.

`ParserModule.friends` is then only overwritten when the module actually
declares friends (`src/compiler/10.frontend/frontend.spl:150-152` is guarded by
`authority_friends.len() > 0 or authority_internal_exports.len() > 0`), so for
the overwhelmingly common case — every file with no `friend` declaration — the
nil survives all the way to surface promotion.

## Why the seed passes and the self-hosted compiler fails

The Rust seed evaluates the declared defaults when lowering the call. The
self-hosted native pipeline relies on `pad_trailing_default_args`
(`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:666-710`),
added for the same defect class in
`native_trailing_default_param_reads_uninitialized_2026-08-09.md`. That pad is
present in the source the stage-2 binary was built from, but it demonstrably
did **not** fire for this cross-module callee — the emitted call is short by two
arguments. Whether the miss is in `direct_call_extern_name`'s key spelling, in
the prescan's module coverage, or in the ambiguity policy is **NOT** established
here and is filed separately (see "Filed, not fixed" below).

## Fix

1. Pass `friends: []` / `internal_exports: []` **explicitly** at every
   `ParserModule` construction site, removing the dependency on a pad that is
   not firing. Four sites:
   - `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl`
   - `src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl`
   - `src/compiler/80.driver/driver_source_pipeline_parsing.spl`
   - `src/compiler/70.backend/backend/compile_c_entry.spl` (neighbour, same
     defect class via `ParserModule`'s defaulted FIELDS)
2. Diagnostic propagation: `module_surface_promote`
   (`src/compiler/20.hir/hir_lowering/module_surface_registry.spl`) collapsed
   thirty distinct causes into one bare `false`. It now records the failing
   field name, exposed as `module_surface_promote_last_failure()`, and the
   driver error reads
   `module surface promotion failed for <path> (field: surface.friends)`.
   Evaluation order and short-circuit behaviour are unchanged.

No check was disabled and no gate was weakened. Promoting a nil is still a
failure — it is now a failure that says which field.

## Guard

`scripts/check/check-parser-module-authority-args-explicit.shs` — fails any
`ParserModule` construction site that omits `friends:` or `internal_exports:`.
Fail-closed: 0 sites found is `ERROR`, never a pass; `--selftest` runs first and
is fatal. Verified FAILing on the pre-fix tree (it independently found a fourth
offender, `driver_source_pipeline_parsing.spl`, that manual inspection missed).

This is a script-level guard rather than a unit spec on purpose: a spec runs
inside an already-deployed `simple` carrying its own compiled `src/compiler`, so
it cannot observe an edit to compiler source and would pass unconditionally.

## Filed, not fixed

- **`pad_trailing_default_args` does not fire for `parser_module_new`.** The
  underlying default-argument lowering defect is still live for other callees.
  Diagnosing it needs a bootstrap cycle: the misbehaviour is baked into the
  stage-2 binary by stage-1 codegen, and small-program `native-build` under the
  stage-2 binary currently SEGVs before MIR (a separate lane's D2), so the
  `SIMPLE_MIR_DEFAULT_PAD_TRACE=1` probe cannot be run on a minimal fixture.
- Not investigated: whether `ParserModule`'s defaulted FIELDS (as opposed to
  `parser_module_new`'s defaulted PARAMS) are lowered correctly. The fix makes
  all four sites explicit, so the question is moot for these two fields but not
  answered in general.
