# Invocation-local function inventory: source review

Baseline commit: `6ea0bd7fa6cb86f3c1abdbd0852fdc5d4eaaa777`.
Baseline tree: `fc99a0f5038663c1db0ded30166d0bd698d92c27`.
Scope: two production source files, one actual-owner differential spec, this
report, and the distinct bug record. No live build input was edited.

## Freeze boundary and mutation proof

The inventory is constructed inside `prescan_module_functions_v1` and is
unreachable after that invocation returns. Its lifetime does not span a
module transformation, another prescan invocation, or persistent cache.
The caller retains the original modules dictionary for the entire loop.

The complete loop body is: obtain scalar tuple; call
`prescan_one_function_v1`; increment position. The scalar accessor only reads
`modules.has`, the selected module's function dictionary, the frozen array,
and nine function fields. No callback, task, external call, sleep or module
writer is introduced. The previous count and new keys length agree for an
unchanged dictionary, including nil-valued rows.

The complete reachable feeder side effects in `prescan_one_function_v1`
(baseline module_lowering 1889–2083) are:

| Call | Reads | Writes |
| --- | --- | --- |
| `register_provider_callable_link_fields_v1` | scalar inputs, symbol display name | `self.callable_link_names`, `self.callable_text_value_abi` |
| `mir_provider_function_name_fields_v1` | linkage attributes, symbol display name | none |
| `get_symbol_raw`, `composite_layout_key`, `mir_class_identity` | module symbol metadata | none |
| `bootstrap_fn_ret_{shape,array_element_shape,err_shape,ok_shape,opt_shape}_register` | scalar names/shapes | corresponding global registry/ambiguity maps and delta journal |
| `bootstrap_fn_param_defaults_register` | parameter/default shape and owner | default/owner/ambiguity registries and delta journal |
| `bootstrap_fn_ret_hir_type_register` | HIR return type | return-type/ambiguity registries and delta journal |
| `bootstrap_fn_param_hir_types_register` | parameter type array | parameter-type/ambiguity registries and delta journal |

The unreachable inline-shield self-call is unchanged. Symbol display lookup
is spelled `me` but its implementation only reads symbols. All bootstrap
registry implementations operate on the `_bootstrap_fn_*` maps/journals;
they never receive the module dictionary or function dictionary. The scalar
feeder receives no module or function dictionary and invokes no function
writer. Stored parameter/type handles are read, not changed. Thus none of
the reachable calls can change this dictionary's membership, values or
key insertion order during the loop. This is a source-level argument,
conditional on the existing runtime honoring its source semantics.

Other `functions` writes found in MIR code are disjoint: `mir_data`'s builder
methods, native-trait thunk publication, global-initializer wrapper creation,
bootstrap MIR publication, module function output assembly and initializer
assembly write **MirModule** dictionaries, not the input **HirModule**
dictionary. `enum_semantic_lowering_v1` constructs a transformed HIR result,
but is not reachable from this feeder. HIR lowering/module-build writes
happen outside this invocation. Driver prescan loops at
`driver_pipeline_lowering.spl:1163,1175,1488` synchronously complete a
prescan before advancing; subsequent transformations get fresh inventories.

## Identity, ordering and scalar semantics

`hc_order_symbol_id_keys_v1` is reused unchanged. It stable-sorts indices;
ties keep the left/source element. It then pushes each original array
element, without a typed SymbolId rebind or `SymbolId(id: ...)`
reconstruction. The caller stores only the resulting array handle locally.
The new accessor uses `module.functions[keys[position]]` directly for the
guard and each field: no named key, HirFunction or HirModule binding.
This preserves the source design's native identity-key requirement.

For every position in the unchanged dictionary the old sorted sequence and
frozen sequence coincide, including ties. Both accessors return the same
nine fields in the same order and the same default tuple on missing/nil/
out-of-range cases. Therefore the unchanged feeder receives the same ordered
argument sequence and performs the same registry operations. Registries
without a reset must not be treated as fresh between differential invocations;
the fixture compares the actual per-owner provider maps and ordered input
tuples, not a purported fresh-process global-registry snapshot.

## Source work counts (not timings)

| F | Old full sorts | New full sorts | Old prefix visits | New row selections |
| ---: | ---: | ---: | ---: | ---: |
| 0 | 0 | 1 empty sort | 0 | 0 |
| 1 | 1 | 1 | 1 | 1 |
| 5 | 5 | 1 | 15 | 5 |
| 1000 | 1000 | 1 | 500500 | 1000 |

Ordering changes from O(F² log F) to O(F log F); selection becomes O(F).
Each nonnil row still performs one guard plus nine dictionary field reads.
Direct indexed key expressions perform a constant number of array accesses
per row; they do not scan earlier rows. There is no explicit clone in the
new accessor. A runtime must still prove array parameters remain handle
transports rather than implicit element copies. Each individual sort uses
O(F) scratch. An arena may retain old per-call allocations until scope end;
their actual lifetime and peak retained storage are unmeasured. This report
does not infer peak RSS from source allocation counts.

## Verification state

Actual-owner fixture cases: empty, singleton, many functions, reverse
dictionary insertion, defaults/params/type payloads, nondefault flags and
attributes, negative/out-of-bound position, missing module, nil-valued row,
and equal numeric SymbolId handles under either identity- or value-keyed
engines. All nine tuple fields are compared against the old implementation.
The actual new prescan is also compared with the old scalar-feeder sequence
for provider map contents and key order, with before/after input inventories.

Runtime specs, branch instrumentation, optimizer CLI, native ABI, core/MCP
smokes, build completion, paired p50/p95 elapsed time, and peak/steady RSS:
**UNRUN**. Only root may schedule the admitted runtime/build lane. No Rust
seed fallback, profiler bypass or second compiler build was used. Source
inspection does not establish the cause of the existing 645 build delay,
an introduced performance regression, or a measured speedup.
