# Bootstrap owner-context inventory v1

Source review only; implementation and executable acceptance pending. Future lineage base `83be266ace4`; frozen campaigns remain immutable.

The transport boundary is an encoded immutable copy. The parent owns mutable registries; a worker resolves references against its admitted retained declaration repository into fresh private owner state. No pointer, full MIR body, global eligibility flag, or digest-only receipt grants lowering authority.

## Function registry

`src/compiler/50.mir/mir_data.spl` owns the following 20 semantic maps. Journal arrays, replacement flags, adoption state and promotion counters are process-local lifecycle state and must not be copied as semantic context.

| Map | Exact value type |
| --- | --- |
| `_bootstrap_fn_ret_types` | `Dict<text, MirType>` |
| `_bootstrap_fn_ret_hir_types` | `Dict<text, HirType>` |
| `_bootstrap_fn_ret_hir_ambig` | `Dict<text, bool>` |
| `_bootstrap_fn_ret_shapes` | `Dict<text, text>` |
| `_bootstrap_fn_ret_shape_ambig` | `Dict<text, bool>` |
| `_bootstrap_fn_ret_array_element_shapes` | `Dict<text, text>` |
| `_bootstrap_fn_ret_array_element_identities` | `Dict<text, text>` |
| `_bootstrap_fn_ret_array_element_shape_ambig` | `Dict<text, bool>` |
| `_bootstrap_fn_ret_ok_shapes` | `Dict<text, text>` |
| `_bootstrap_fn_ret_ok_shape_ambig` | `Dict<text, bool>` |
| `_bootstrap_fn_ret_err_shapes` | `Dict<text, text>` |
| `_bootstrap_fn_ret_opt_shapes` | `Dict<text, text>` |
| `_bootstrap_fn_ret_opt_shape_ambig` | `Dict<text, bool>` |
| `_bootstrap_fn_param_hir_types` | `Dict<text, [HirType]>` |
| `_bootstrap_fn_param_hir_rejected` | `Dict<text, bool>` |
| `_bootstrap_fn_param_defaults` | `Dict<text, [HirParam]>` |
| `_bootstrap_fn_param_defaults_ambig` | `Dict<text, bool>` |
| `_bootstrap_fn_param_default_owners` | `Dict<text, text>` |
| `_bootstrap_default_provider_symbols` | `Dict<text, SymbolTable>` |
| `_bootstrap_default_provider_globals` | `Dict<text, [HirConst]>` |

Each scalar ambiguity/rejection map remains authoritative even if its typed-value row is absent. Default owner, default parameter expressions, provider symbols and provider globals must be transported together; matching arity/default flags does not establish declaration equivalence. Map rows require duplicate/conflict rejection, canonical order, aggregate count/byte/allocation bounds and installation only after complete decode and reference validation.

## Callable/static owner

`src/compiler/50.mir/_MirLowering/bootstrap_globals.spl` owns `_bootstrap_callable_link_names`, `_bootstrap_callable_text_value_abi` and `_bootstrap_function_value_names`, plus parallel static metadata arrays (`modules`, `symbol_ids`, `names`, `type_tags`, `init_kinds`, `init_payloads`, `alignments`, `visibilities`, `externals`) and module-count state.

Its `_bootstrap_mir_function_names/modules/return_type_tags/return_unsigned/param_starts/param_counts/param_type_tags` arrays share indexes with `_bootstrap_mir_functions`. They are emitted-body state, not a declaration-only owner. Importing parent arrays without bodies would make `bootstrap_mir_function_at` invalid. C confirmed worker selected bodies must reset/populate these arrays themselves. Do not serialize MIR functions to hide this distinction. Any separate declaration lookup projection needs an explicit consumer and semantic equivalence proof.

## Enum/composite owner

`src/compiler/50.mir/_MirLowering/bootstrap_type_registration.spl` owns `_bootstrap_type_runtime_names`. Actual enum runtime identities, discriminants, qualified/bare collision policy, provider order and composite layout maps reside in each `MirLowering`, populated by `prescan_module_declarations_v1` and the existing registration methods. Reconstruct them against fresh private lowering owners by replaying the exact admitted declaration order. Transport builtin Result/Option identities and preserve module-local shadowing; a runtime-name map alone is insufficient evidence.

## Shared API agreement and prerequisite

B owns opaque canonical SDN context receipts for exactly ordered `function_registry`, `callable_registry`, `enum_composite`. Proposed A DTO is `BootstrapOwnerSnapshotV1(body:text,digest:text,bytes:i64,rows:i64)`; C must compare actual installed/re-exported receipts with B's sealed digests/bytes/rows before bootstrap lowering. Typed reconstruction needs the admitted repository; enum replay additionally needs a fresh lowering owner and exact source order. API signatures remain pending exact provenance design and review; no callable stub APIs have been added.

Astra approved exact retained declaration/artifact references instead of a custom 20-map HIR codec. References must bind repository authority, module/function/parameter identity and complete declaration digest, and reject missing or ambiguous resolution. Existing typed registry register APIs do not retain declaration origins, especially for lowered MirType returns. Conservative inference cannot replace missing provenance. Future-lineage explicit origin capture versus unique admitted-repository resolution requires review before source edits.

Canonical generated HIR decoding is a prerequisite owned by `gh_phase3_fix_refresh`: `hir_canonical_codec_generated_available_v1()` is explicitly false; generated `hc_dec_hir_type`, `hc_dec_symbol_table`, `hc_dec_hir_expr` and `hc_dec_hir_module` lack a complete depth/preallocation guard closure. Their declaration/default/selective-body consumers do not gain bounds from a postdecode roundtrip. Do not bypass this refusal or flip the global availability flag.

No owner snapshot/import, serial-prescan equivalence, bootstrap worker route, or full SOURCE acceptance is claimed by this inventory.

## Finite provenance foundation

The foundation now records immutable registration metadata beside actual semantic map writes. Declaration prescan uses explicit module-function array indexes to fetch the real return/parameter fields; no public ambient origin setter or inference scan is introduced. Identical parameter registrations keep the original event; ambiguity removes observable evidence; a changed legacy registration revokes prior evidence. The other typed compatibility registrars have revocation hooks but no claimed bound-reference export yet.

Origins are prepaid against a conservative 64 MiB lifetime metadata ledger and one million captured events. Exhaustion permanently makes provenance unavailable for that process while ordinary registries keep their prior semantics. Existing transient journals retain newly allocated origin records, and the normal promotion barrier adopts them; abandoned-delta cleanup revokes availability without dereferencing released records. No ordinary unbound registration allocates provenance while no checked origin exists. New frontend-based unit controls cover actual field capture, winner preservation, changed unbound writes, ambiguity, missing metadata and transient scope lifetime. Their constructed binding labels are mechanics only and grant no retained-repository or SOURCE authority. Controls and compiler checks remain UNRUN: this isolated checkout has no admitted self-hosted CLI binary.

Transport export/import, all six typed-owner reference factories, enum/composite replay equivalence and atomic private-owner installation remain unfinished. Worker eligibility stays unchanged. The transitive canonical decoder prerequisite is authored by its separate owner but not admitted merely by source review.

### Reviewed lifecycle correction

Astra found that `bootstrap_fn_registries_discard_delta_v1` runs at every normal scoped-module start, not only an abort. The correction tracks a persistent scalar pending-origin delta: actual in-scope origin writes set it; only successful promotion clears it; discard revokes only when that pending delta was abandoned. Neither normal begin nor failed cleanup dereferences a prior released journal. A scalar inserted-row count replaces unreliable native `Dict.len()` in the empty-origin fast path and changes only after a real first insertion.

The unit spec now calls actual `lower_module_transient_scoped` on two frontend-produced ordinary modules and checks that prior origins survive both normal begin/promotion lifecycles. The permanent-abort negative is an explicit standalone fixture (`test/fixtures/compiler/bootstrap_fn_registration_origin_abort_control.spl`), so revocation does not contaminate aggregate specs. It must be executed through the qualified existing Simple CLI in a fresh process; no replacement runner or seed is supplied. These new controls remain UNRUN.
