# MCP native build: `method 'contains' not found on type 'nil'` immediately after monomorphization

**Date:** 2026-09-01 · **Status:** OPEN · **Severity:** blocker (last thing between the MCP build and MIR lowering)

## Provenance
HEAD `ec054763e96` (on top of `9fb0d279739`), seed
`src/compiler_rust/target/release/simple.exe` md5
`286f66b8615dce0e0da788f0550c4008`. `SIMPLE_EXECUTION_MODE=interpret`,
`SIMPLE_NATIVE_BUILD_WORKER=1`, `SIMPLE_RESOLVE_METHODS` unset (default OFF).

```
bin: simple.exe run src/app/cli/native_build_worker.spl src/app/mcp/main.spl
```

## How far the build now gets (rc=1, ~21 min)
```
step 1/6 parse           100/100 OK
step 1/6 surface_build   100/100 OK
step 2/6 hir             100/100 OK        [hir-cache] hits=100 misses=0
         any-escape pass      548 diagnostic(s)   (warnings)
         enum-contract pass     0 diagnostic(s)
         [mono] generic_fns=0 call_sites=0 specializations=0 unresolved=0
         0 compile errors  (SIMPLE_DUMP_COMPILE_ERRORS=1 -> zero [compile-error] lines)
error: semantic: method `contains` not found on type `nil` (receiver value: nil)
```
This is the FIRST time the build has cleared HIR entirely. It dies between the
`[mono]` receipt (`driver_hir_pipeline_passes.spl:129`) and MIR lowering, so the
candidate region is the `mono_diags` loop, `record_pass_receipt`, or
`post_mono_verify_modules` / `post_mono_report_*` that follow it
(`driver_hir_pipeline_passes.spl:129-175`).

## Not yet pinned
`SIMPLE_DEBUG_FIELD_ACCESS=1` and `SIMPLE_INTERP_OOB_DEBUG=1` print NOTHING for
this one — the seed's `[field-access-error]` probe covers field access, not a
method-not-found on a nil receiver. There is no equivalent
`[method-call-error]` dump. Next step is either to add one to the seed, or to
bisect with `eprint` probes across `driver_hir_pipeline_passes.spl:129-175`
(each full run costs ~21 minutes; surface_build alone is ~19 of them).

## Defect family
Same shape as the two already fixed today: a provider returns nil/a status
where the caller expects a collection, and the member access is fatal. See
`doc/08_tracking/bug/mcp_native_build_hir_entry_env_get_nil_len_fatal_2026-09-01.md`
and `doc/08_tracking/bug/self_rooted_chain_val_binding_clobbers_receiver_2026-09-01.md`.

## MIR error count
Still NOT obtainable — MIR lowering (step 3+/6) is never entered. The last
real full-build number remains 133, measured before this lane's fixes.

## Lead REFUTED by experiment (2026-09-01)
Hypothesis: the nil receiver was one of the three `text.contains(...)` calls in
`src/compiler/40.mono/verify/post_mono_verify.spl`
(`check_mangling` lines 586/590, `enter` line 603) reached with a nil HIR
definition name. All three were nil-guarded (`?? ""`) and the full build re-run:
**identical failure, same message, same position** (hir 100/100, any-escape 548,
enum-contract 0, `[mono] generic_fns=0`, then
`error: semantic: method \`contains\` not found on type \`nil\``).
The guards were therefore REVERTED rather than left as speculative dead
robustness. The site is elsewhere in the post-mono -> MIR-entry region, and the
region is wider than the "129-175" first written above: no receipt prints
between the `[mono]` line and the (never reached) step 3/6 announcement, so
nothing bounds it at 175.

Next lead, in cost order:
1. add a `[method-call-error]` dump to the seed's method-not-found path — the
   sibling of the existing `[field-access-error]`, which is what pinned the HIR
   blocker in minutes; it prints nothing for a method-not-found today;
2. failing that, `eprint` bisection across the post-mono region (~21 min/run).

## `SIMPLE_DUMP_COMPILE_ERRORS` gate verified both ways (2026-09-01)
The gate reads the ambiguous `env_get` (6 co-compiled defs, 2 signatures), so it
was tested rather than assumed, using the worker on a 2-line file with a
deliberate unresolved name:
- `SIMPLE_DUMP_COMPILE_ERRORS=1` -> `[compile-error] HIR lowering error ...:
  unresolved name: definitely_not_a_real_symbol` (1 line), then the usual
  `phase 3 FAILED (diagnostics unreadable...)`;
- unset -> **0** `[compile-error]` lines.
So the dump fires when asked and is silent by default.

## CORRECTION 2026-09-02: `SIMPLE_INTERP_OOB_DEBUG=1` DOES print — the earlier run lost stderr

The "Not yet pinned" section above is **wrong** and must not be used to plan.
It states that `SIMPLE_INTERP_OOB_DEBUG=1` prints NOTHING for this failure and
concludes that the next step is "either to add a `[method-call-error]` dump to
the seed, or to bisect with `eprint` probes ... (~21 minutes per run)". Both
halves are false, and the seed-patch lead is unnecessary work.

**The probe already exists, is unconditional on this exact path, and is in the
deployed seed.**

- The failing message is constructed at
  `src/compiler_rust/compiler/src/interpreter_method/mod.rs:1744` and `:1755`.
  That is the ONLY site in the tree that appends the ` (receiver value: ...)`
  suffix (`/usr/bin/grep -rn "receiver value" src/compiler_rust --include=*.rs`
  -> the only construction site is `mod.rs:1736`), so the failure is pinned to
  this function without any further experiment.
- The `SIMPLE_INTERP_OOB_DEBUG` block sits at `mod.rs:1715-1731`, i.e. between
  the last fallback (`try_bare_some_option_method`) and the error construction,
  with **no early return between them**. If the error is raised, the block ran.
- The deployed seed carries it: `grep -c "mnf-debug"
  src/compiler_rust/target/release/simple.exe` -> **3** (same seed,
  md5 `286f66b8615dce0e0da788f0550c4008`).

**Validated end to end on a 4-line repro** (30 seconds, not 21 minutes), with
`SIMPLE_EXECUTION_MODE=interpret SIMPLE_INTERP_OOB_DEBUG=1
SIMPLE_DEBUG_FIELD_ACCESS=1`:

```
fn give() -> str?:
    return nil

fn probe_it():
    val v = give()
    print(v.contains("x"))

probe_it()
```

stderr (rc=1):

```
[mnf-debug] method=contains recv_type=enum recv=Option::None
[mnf-debug-spl] probe_it
[mnf-debug-bt]    0: <unknown>
[mnf-expr] method=contains recv_expr=Identifier("v")
error: semantic: method `contains` not found on type `enum` (receiver value: Option::None)
```

So the seed emits **three** useful facts for free: the interpreted `.spl`
frame (`[mnf-debug-spl]`), the receiver EXPRESSION (`[mnf-expr]`), and the
receiver's runtime type/value. `[mnf-expr]` is not mentioned anywhere in this
record and is the single most useful line for locating the call site.

Why the earlier run saw nothing: these go to **stderr**, and the earlier
invocation did not capture it separately (the wrapper truncates fatal output —
see the brief's own warning to drive `native_build_worker.spl` directly). This
is a captured-output defect, not a missing probe.

**Do not patch the seed for this.** Re-run the worker with both env vars and
`2> <file>`.

Note the repro renders as type `enum` / `Option::None` while the MCP build
reports type `nil`; both reach the same construction site (`Value::Nil` vs a
`None`-shaped enum receiver), so the probe fires for both.

Provenance of this correction: HEAD `27c89536f8c`, 89 dirty paths, seed
`src/compiler_rust/target/release/simple.exe` md5
`286f66b8615dce0e0da788f0550c4008` (39,120,896 bytes).

## PINNED AND FIXED 2026-09-02 — the site is inside MIR lowering, not before it

Re-ran the worker with `SIMPLE_INTERP_OOB_DEBUG=1 SIMPLE_DEBUG_FIELD_ACCESS=1`
and stderr captured to a file (35 min, rc=1). The probe answered immediately:

```
[mnf-debug] method=contains recv_type=nil recv=nil
[mnf-debug-spl] main -> cli_native_build -> compiler_driver_run_compile -> compile
  -> aot_compile -> lower_to_mir -> lower_to_mir_with_target_context
  -> lower_module -> lower_function -> lower_function_with_gpu_metadata
  -> lower_block -> lower_block_expected -> lower_expr -> lower_expr_impl
  -> try_lower_global_read -> find_global_static
[mnf-expr] method=contains recv_expr=Identifier("__nested_field_global_statics_by_id__")
error: semantic: method `contains` not found on type `nil` (receiver value: nil)
```

**Two corrections to this record's earlier framing.** The failure is NOT
"between the `[mono]` receipt and MIR lowering" — it is INSIDE `lower_to_mir`,
several frames deep. And the candidate region named earlier
(`driver_hir_pipeline_passes.spl:129-175`, `post_mono_verify_modules`) was never
on the path, which is why the post_mono_verify guard experiment was refuted.

### Root cause (confirmed, contained)

`MirLowering.global_statics_by_id` and `.global_constants_by_id` are declared in
`src/compiler/50.mir/mir_lowering_types.spl:424-425` with no default, and were
initialised **nowhere in the tree**:

- absent from the ONLY constructor call, `MirLowering.new_for_target`
  (`src/compiler/50.mir/_MirLowering/module_lowering.spl:253`), which does
  initialise the neighbouring `global_symbol_ids`, `global_const_exprs` and
  `array_global_mutation_warned`;
- the only two assignments in the tree
  (`_MirLoweringExpr/switch_operators_calls.spl:4468-4469`) copy `self`'s
  already-nil value into a sub-lowerer, so they propagate the defect rather
  than fix it.

Every `MirLowering` therefore carried both fields as `Value::Nil` for its whole
life, and the first read — `self.global_statics_by_id.contains(symbol_id)` at
`_MirLoweringExpr/expr_dispatch.spl:223`, inside `find_global_static` — was
fatal. Omitting a `Dict` field from a constructor call yields nil, not an empty
dict, so the mistake is silent at construction and only fatal at first use; the
desugared receiver name `__nested_field_<field>__` in the diagnostic does not
textually match the use site, which is why it misdirected earlier readers.

### Fix
Initialise both fields in `MirLowering.new_for_target`
(`module_lowering.spl:326`). One-line-per-field, no behaviour change for any
already-working path.

### The record's own bool-set workaround advice was stale, and is corrected
`mir_lowering_types.spl:405-412` claimed that naming such a field in the
constructor STILL leaves it nil, and recommended a bool-set instead. That does
not reproduce on this seed for a struct-valued `Dict<i64, Struct>` field —
measured directly (4 examples, 0 failures). The comment is corrected in place.

### Specs
- reproducing: `test/01_unit/compiler/50.mir/mir_lowering_global_maps_initialized_spec.spl`
  (4 examples, 0 failures)
- generalizing: `test/01_unit/compiler/50.mir/struct_collection_field_construction_contract_spec.spl`
  (7 examples, 0 failures) — sweeps element kinds, access forms, and the
  field-to-field copy shape from `switch_operators_calls.spl:4468`.

### Separate defect found while writing the generalization spec
`Dict<i64, _>.keys()` yields text-typed keys, so summing them concatenates
(`0 + 1 + 2` -> `"012"`). Reproduces on a plain local dict, unrelated to struct
fields. Filed as
`doc/08_tracking/bug/dict_i64_keys_sum_concatenates_as_text_2026-09-02.md`.

### MIR error count
Still not produced by THIS run — the build aborted at the first
`find_global_static` call, so MIR lowering never completed and no error count
exists. A verification build with the fix is in flight; the count will be
recorded when it lands. The last real full-build number remains **133**, and
nothing in this record supersedes it.

## Latent population: 16 MORE MirLowering fields are nil for the same reason

Audited 2026-09-02 by diffing the struct's declared field names
(`mir_lowering_types.spl`, 97 fields) against the argument names of its only
constructor call (`module_lowering.spl:253`, 81 arguments after this fix). The
16 below are declared with **no default** and passed by **no constructor
argument**, so they are `Value::Nil` at runtime exactly as
`global_statics_by_id` was:

```
finally_stack: [HirBlock]                 (line 56)
type_transport_receipts: i64              (67)
type_transport_owner: text                (68)
type_transport_context: text              (69)
type_transport_param_index: i64           (70)
mcdc_mode: i64                            (75)
mcdc_owner_bytes: i64                     (76)
mcdc_global_bytes: i64                    (77)
mcdc_include_csv: text                    (78)
mcdc_exclude_csv: text                    (79)
mcdc_next_runtime_id: i64                 (80)
mcdc_active_decision_id: i64              (81)
mcdc_active_decision_semantic: text       (82)
mcdc_next_condition_ordinal: i64          (83)
mcdc_active_dynamic_token: LocalId        (84)
mcdc_active_tokens: [LocalId]             (85)
```

None was touched by this fix, deliberately: only the two that demonstrably
aborted the build were changed, and blanket-initialising 16 fields (one of
which, `mcdc_active_dynamic_token: LocalId`, has no obvious zero value) is a
larger change than the blocker warranted. They are recorded here because they
are the next candidates the moment MIR lowering reaches a function that reads
one — most plausibly `finally_stack`, which any `try`/`finally` lowering would
touch, and the `type_transport_*` group. The `mcdc_*` group is coverage
instrumentation and is likely unreachable with MC/DC off.

The general lesson, and the reason the generalization spec exists: a struct
field with no default that no constructor argument names is silently nil, and
NOTHING in the tree reports it — not construction, not the type checker. The
audit above is a two-command diff and should be re-run whenever a field is added
to this struct.
