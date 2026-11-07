# Bootstrap constant recovery loses export visibility

Status: source repair and prevention controls authored; runtime NOT_RUN.

At release `266b0afb7344f7856320e01b414a7a56b39ff8db`, `lower_parser_module_unstub` first calls `lower_module`, then unconditionally rebuilds constants in bootstrap mode. That recovery used raw `lower_hir_const_decl`, losing the export-list visibility lift introduced by PR #7331. The normal recovery already uses `hir_const_with_export_visibility`.

The repair snapshots the module export names and reuses that same helper in bootstrap recovery and the direct `lower_module` bootstrap constants block. It preserves the existing rule: lift only Private mutable statics; retain explicit scoped visibility and the immutable literal path. Both Public visibility and `is_public` remain aligned for linkage and interface identity. No symbol-allocation or visibility API changes are introduced.

Production driver paths in `driver_hir_pipeline_lowering.spl` call `lower_parser_module_unstub`; the regression fixture invokes this owner with real parsed declarations and observes bootstrap mode. Four scenarios cover wrapper and direct entry, each in bootstrap and normal modes. Each requires four exact names, mutable/public flags and neighboring exclusions. Runtime, native compilation, docgen and full compiler/core/MCP checks remain NOT_RUN.

Direct production calls remain in `driver_hir_pipeline_lowering.spl`'s bootstrap module loop and compatibility loop (base lines 1737 and 2622). They disable ambient bootstrap only when `driver_hir_explicit_semantic_policy` selects that policy; they do not pass through the wrapper. The second repaired constants block covers those direct calls. By contrast, `driver_frozen_semantic_prerequisites_v1.spl` explicitly disables ambient bootstrap before its direct call. This closes the two identified source omissions, not runtime qualification of those callers. PR #7300's existing six T32 `pub var` declarations are another owner's active workaround; this patch neither adopts nor supersedes that PR automatically.
