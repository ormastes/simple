# MIR lowering rejects a cross-module struct field default `= None` as `HirExprKind.Error`

- Status: open (worked around at the only `src/` construction site)
- Found: 2026-11-19 (native Stage 2 full-CLI build, "Phase 4", go-to-end mode)
- Component: `src/compiler/50.mir` (struct-literal lowering of omitted defaulted fields)

## Symptom
```
[go-to-end] failed stage=mir module=lib.nogc_sync_mut.orchestration.host_linux_service_agent_v4: MIR lowering error: unsupported provider default for src/lib/nogc_sync_mut/orchestration/host_agent_attachment_v4.spl::HostAgentAttachmentV4.helper; supply the field explicitly at src/lib/nogc_sync_mut/orchestration/host_agent_attachment_v4.spl:112:41
failed stage=mir module=lib.nogc_sync_mut.orchestration.host_linux_service_agent_v4: MIR lowering error: MIR lowering produced no local for this expression
```
The second line follows from the first: the struct literal returns `None` after
`error_fatal`, so its enclosing `Some(...)` has no local.

## Where the error is raised
`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` (~7045): when a
struct literal omits a field whose `struct_field_has_default` flag is set, the
lowering calls `resolve_struct_field_default_expr_v1(struct_name, fi)` and treats a
result of kind `HirExprKind.Error` as fatal ("unsupported provider default ...").
The field here is `helper: Option<HostHelperLeaseV1> = None`
(`host_agent_attachment_v4.spl:112`). It is the first defaulted field of
`HostAgentAttachmentV4`, and lowering stops at the first failure, so the other
`None`-defaulted fields (`session`, `cleanup_spawn`, `native_retirement`,
`settlement`, `geometry`, `pane_writes`) were never reached. They probably fail
the same way.

## Probable mechanism (brief reading, not confirmed by a build)
`resolve_struct_field_default_expr_v1`
(`src/compiler/50.mir/_MirLowering/declaration_providers_v1.spl:319`) takes the
declaration-repository path. It calls `load_declaration_field_default_v1`, then
`load_declaration_expression_v1`. That function loads the archived HIR artifact
for the default. For a foreign owner module, it then rebinds the artifact with
`remap_declaration_default_expr_v1`
(`_MirLowering/declaration_default_rewrite_v1.spl`).

The rebind can produce `Error` in two ways:

1. **Relocation failure.** The `NamedVar` arm sets `Error` when
   `declaration_default_reference_v1` returns id < 0. The builtin `None` path
   (`consumer_builtin_none_symbol_v1`, `provider_metadata.spl:656`) returns -1
   when the consumer table already binds `None` to a module-owned or non-function
   symbol. But every id < 0 path also calls `declaration_default_fail_v1`, which
   reports its own `error_fatal` and sets `frame.failed`. Because
   `MirHirDefaultBindingFrameV1` is a class, the flag propagates, and
   `load_declaration_expression_v1` returns `None` rather than an `Error`
   expression. This path therefore does not match the observed message.
2. **Error already in the archived artifact (most likely).** The remap treats
   `HirExprKind.Error` as a leaf (`declaration_default_rewrite_v1.spl:527`). It
   passes it through without failing the frame. So if the provider's HIR lowering
   stored the `= None` field default as `Error`, the consumer gets that `Error`
   back silently, and the struct-literal site reports exactly "unsupported
   provider default". A matching earlier case supports this. `MirBuilder` in
   `src/compiler/50.mir/mir_data.spl:195` has to supply `loop_view_capture_v1:
   None` explicitly for the same message, and that is a same-module case: there
   is no remap at all. That points at the HIR-side capture/archival of a bare
   `None` field default, not at cross-module relocation.

Fix direction: find where the HIR artifact for a struct field default is
produced, and why a bare `None` (no expected-type context at the field-default
site?) becomes `Error` there. A silent `Error` leaf in an archived default
should also fail at archive time instead of surfacing at a consumer.

## Workaround
`src/lib/nogc_sync_mut/orchestration/host_linux_service_agent_v4.spl`,
`host_agent_attach_archived_v4`, is the only `src/` site that constructs
`HostAgentAttachmentV4` (`git grep -n 'HostAgentAttachmentV4('`; the other hits
are unit specs; there are no `.default`/spread forms). It now supplies all 38
fields. The 24 previously omitted fields use their declared defaults copied
verbatim, so the semantics are unchanged. The site is tagged
`@workaround bug=mir_cross_module_struct_field_default_error_2026-11-19`.
Remove the extra arguments once MIR lowers these defaults.
