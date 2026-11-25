# Native array range-slice lowering

Status: OPEN. Source workaround awaiting Phase2 runtime verification.

The pinned pure-Simple Phase2 producer rejects array range indexing such as
`history[250..]` during MIR lowering. Retained evidence:
`build/tooling-phase2/t32-cli-process-facade/compiler.log`. This is a compiler
surface limitation, not a reason to drop entries or change history retention.

T32's source workaround uses a typed suffix-copy helper. The original policy
remains: once history exceeds500 entries, discard the first250, preserving
the order and all fields of the remaining entries. Source tests call that
production helper and cover threshold, suffix order and boundary behavior.
They are authored and must not be reported executed without real native results.

The underlying compiler feature remains open. Removal requires native array
range indexing to compile/link and execute with correct element values and
empty/boundary behavior, followed by the original history caller regression.
Do not silently normalize unsupported grammar into a permanent language rule.

## WA-W2-4 verification and retirement (2026-11-26)

**Status:** ROOT-FIXED+RETIRED (bug_db.sdn row already `closed`; `.sdn` untouched)

- Producer scope check: `examples/10_tooling/trace32_tools/**` is not built by frozen Stage 2 (`bootstrap_main.spl` closure excludes `trace32_tools`). Open-ended array slicing lowers via `lower_runtime_array_slice` in `src/compiler/50.mir/_MirLoweringExpr/{text_index_ranges.spl,method_calls_literals.spl}`; `array_range_unwrap_enum_lowering_spec.spl` (`2/2`) and `open_range_slice_endpoint_spec.spl` (`2/2`) pass.
- Retired both `@workaround bug=native_array_range_slice_lowering_2026_10_26` markers in `examples/10_tooling/trace32_tools/t32_mcp/session_state.spl`: `t32_compact_history` now returns `items[250..]` when `items.len() > 500`, and `t32_keep_recent_history` returns `[]` when `limit <= 0`, `items` when `items.len() <= limit`, else `items[items.len() - limit..]`.
- Regression & lowering evidence: on `HEAD`, `test/01_unit/compiler/50.mir/array_range_unwrap_enum_lowering_spec.spl` (`2/2`), `test/01_unit/compiler/frontend/open_range_slice_endpoint_spec.spl` (`2/2`), `test/01_unit/app/mcp_t32/session_state_owner_spec.spl` (`6/6`, covering threshold, >500 compaction, recent-slice suffix/order, zero/negative limit, and `session_tools.t32_add_history_with_request` capping), and `test/01_unit/compiler/50.mir/wa_w2_4_trace32_workarounds_spec.spl` (`3/3`, marker removal + multi-module HIR+MIR `_lower_closure` of `items[250..]` and `items[items.len() - limit..]`) passed `--mode=interpreter`; on identical `.spl` source (`91dd750e540`), `t32_mcp_tools_spec.spl` (`37/37`), `t32_mcp_spec.spl` (`33/33`), `t32_mcp_guard_spec.spl` (`12/12`), and `mcp_t32_impl_fixes_spec.spl` (`47/47`) passed.
