# MCP/LSP/DAP Integration - Documentation Index

**Last Updated**: 2026-02-04
**Phase**: Phase 1 Complete ✅

---

## Quick Links

### Reports & Analysis
- **[Phase 1 Completion Report](report/mcp_lsp_dap_phase1_completion_2026-02-04.md)** - Phase 1 summary and next steps
- **[Integration Analysis](research/mcp_lsp_dap_integration_analysis.md)** - Full 6-phase roadmap and architecture

### Implementation
- **[Compiler Query API](../src/compiler/query_api.spl)** - LSP integration API (450 lines)
- **[Interpreter Hook API](../src/runtime/hooks.spl)** - DAP integration API (550 lines)

### Guides
- **[Compiler Query API Guide](guide/compiler_query_api_guide.md)** - Complete API reference for LSP
- **[Interpreter Hooks Guide](guide/interpreter_hooks_guide.md)** - Complete API reference for DAP
- **[MCP Setup Guide](guide/mcp_setup_and_usage.md)** - Existing MCP server documentation

### Existing Implementations
- **[MCP Server](../src/app/mcp/main.spl)** - Complete, self-hosted in Simple
- **[LSP Server](../src/app/lsp/)** - Phase 1 complete (protocol layer)
- **[DAP Server](../src/app/dap/)** - Phase 1 complete (protocol layer)

---

## Status Summary

| Component | Status | Phase | Next Steps |
|-----------|--------|-------|------------|
| **MCP** | ✅ Complete | Production | Add Resources + Prompts (Phase 2) |
| **LSP** | ⚠️ Partial | Phase 1/4 | Integrate Query API (Phase 3) |
| **DAP** | ⚠️ Partial | Phase 1/4 | Integrate Hook API (Phase 4) |
| **Query API** | ✅ Designed | Design | Implement FFI (Phase 3) |
| **Hook API** | ✅ Designed | Design | Implement FFI (Phase 4) |

---

## Phase Overview

### ✅ Phase 1: Foundational APIs (COMPLETE)
- **Duration**: 4-6 weeks
- **Deliverables**:
  - ✅ Compiler Query API design
  - ✅ Interpreter Hook API design
  - ✅ Comprehensive documentation (1,450+ lines)
  - ✅ Integration roadmap
  - ✅ FFI requirements (24 functions)

### 📝 Phase 2: MCP Enhancement (NEXT)
- **Duration**: 2-3 weeks
- **Goal**: Add Resource and Prompt support
- **Tasks**:
  - Implement `ResourceManager`
  - Implement `PromptManager`
  - Update MCP server
  - Add progress notifications

### 📝 Phase 3: LSP Phase 2
- **Duration**: 3-4 weeks
- **Goal**: Code completion, hover, go to definition
- **Tasks**:
  - Implement Query API FFI
  - Integrate with LSP server
  - Add completion support
  - Add navigation features

### 📝 Phase 4: DAP Phase 2
- **Duration**: 2-3 weeks
- **Goal**: Real debugging with interpreter integration
- **Tasks**:
  - Implement Hook API FFI
  - Integrate with DAP server
  - Add breakpoint triggering
  - Add stack frame capture

### 📝 Phase 5: LSP Phase 3
- **Duration**: 4-6 weeks
- **Goal**: Find references, symbols, semantic tokens
- **Tasks**:
  - Advanced LSP features
  - Workspace support
  - Performance optimization

### 📝 Phase 6: DAP Phase 3-4
- **Duration**: 4-5 weeks
- **Goal**: Expression evaluation, watches
- **Tasks**:
  - Advanced debugging features
  - Expression evaluator
  - Conditional breakpoints

**Total Timeline**: 19-27 weeks (~5-7 months)

---

## API Reference Quick Links

### Compiler Query API

**Entry Point**: `CompilerQueryContext.create(project_root)`

**Key Methods**:
- `parse_file(path)` - Parse and cache AST
- `symbol_at(path, pos)` - Get symbol at position
- `find_definition(path, pos)` - Go to definition
- `find_references(path, symbol)` - Find all references
- `completions_at(path, pos)` - Code completions
- `hover_at(path, pos)` - Hover information
- `get_diagnostics(path)` - Parse/type errors
- `document_symbols(path)` - Document outline

**Types**: `Position`, `Symbol`, `Completion`, `Diagnostic`, `HoverInfo`

### Interpreter Hook API

**Entry Point**: `InterpreterHookContext.create()`

**Key Methods**:
- `add_breakpoint(file, line)` - Add line breakpoint
- `add_breakpoint_with_options(...)` - Conditional/log breakpoint
- `continue()` - Resume execution
- `step_over()`, `step_into()`, `step_out()` - Step execution
- `stack_frames()` - Get current stack
- `variables_in_frame(frame_id)` - Inspect variables
- `evaluate(expr, frame_id)` - Evaluate expression
- `set_event_callback(fn)` - Handle debug events

**Types**: `Breakpoint`, `StackFrame`, `Variable`, `EvalResult`, `DebugEvent`

---

## FFI Requirements

### Query API FFI (11 functions)
**Location**: `rust/compiler/src/query_ffi.rs` (to be created)

- Parsing: `rt_parse_source`, `rt_get_file_mtime`
- Symbols: `rt_build_symbol_table`, `rt_find_symbol_at_position`, etc.
- Type checking: `rt_type_check_ast`
- Completions: `rt_get_context_keywords`

### Hook API FFI (13 functions)
**Location**: `rust/compiler/src/interpreter_hooks.rs` (to be created)

- Breakpoints: `rt_hook_add_breakpoint`, `rt_hook_remove_breakpoint`, etc.
- Execution: `rt_hook_continue`, `rt_hook_pause`, `rt_hook_step`, etc.
- Stack: `rt_hook_get_stack_frames`, `rt_hook_get_call_depth`
- Variables: `rt_hook_get_variables`
- Evaluation: `rt_hook_evaluate_expression`, `rt_hook_evaluate_condition`

---

## Architecture Diagram

```
                    ┌─────────────────────────────┐
                    │   Simple Compiler Core      │
                    │  (Parser, Type System,      │
                    │   Symbol Tables, HIR/MIR)   │
                    └───────────┬─────────────────┘
                                │
                  ┌─────────────┼─────────────┐
                  │             │             │
         ┌────────▼────────┐   │   ┌────────▼────────┐
         │   LSP Server    │   │   │   DAP Server    │
         │  (IDE Support)  │   │   │   (Debugging)   │
         └────────┬────────┘   │   └────────┬────────┘
                  │            │            │
                  │            │            │
         ┌────────▼────────────▼────────────▼────────┐
         │   Compiler Query API    Hook API          │
         │  (query_api.spl)     (hooks.spl)          │
         └────────┬──────────────────────────────────┘
                  │
         ┌────────▼────────┐
         │   MCP Server    │
         │ (Tool/Resource  │
         │   Integration)  │
         └─────────────────┘
```

---

## Getting Started

### For LSP Development

1. Read: [Compiler Query API Guide](guide/compiler_query_api_guide.md)
2. Review: [Query API Implementation](../src/compiler/query_api.spl)
3. Check: [Integration Analysis](research/mcp_lsp_dap_integration_analysis.md#lsp-language-server-protocol-analysis)

### For DAP Development

1. Read: [Interpreter Hooks Guide](guide/interpreter_hooks_guide.md)
2. Review: [Hook API Implementation](../src/runtime/hooks.spl)
3. Check: [Integration Analysis](research/mcp_lsp_dap_integration_analysis.md#dap-debug-adapter-protocol-analysis)

### For MCP Enhancement

1. Read: [MCP Setup Guide](guide/mcp_setup_and_usage.md)
2. Review: [Current MCP Server](../src/app/mcp/main.spl)
3. Check: [Gap Analysis](research/mcp_lsp_dap_integration_analysis.md#mcp-model-context-protocol-comparison)

---

## Testing

### Unit Tests

**LSP**: `test/lib/std/unit/lsp/query_api_spec.spl` (to be created)
**DAP**: `test/lib/std/unit/dap/hook_api_spec.spl` (to be created)
**MCP**: `test/lib/std/unit/mcp/*_spec.spl` (existing)

### Integration Tests

**LSP**: Test with VS Code / Neovim
**DAP**: Test with VS Code / Neovim debugger
**MCP**: Test with Claude Code CLI

---

## Performance Targets

| Operation | Target | Component |
|-----------|--------|-----------|
| Code completion | < 50ms | LSP |
| Hover information | < 20ms | LSP |
| Diagnostics | < 200ms | LSP |
| Find references | < 500ms | LSP |
| Breakpoint hit | < 10ms overhead | DAP |
| Stack frame capture | < 50ms | DAP |
| Variable inspection | < 100ms | DAP |
| Expression evaluation | < 100ms | DAP |

---

## Key Decisions

### Design Philosophy

1. **Incremental**: Parse only what's needed, cache results
2. **Fast**: Response time targets for real-time IDE feedback
3. **Resilient**: Work with partial/broken code
4. **Safe**: Cannot crash interpreter
5. **Non-intrusive**: Minimal overhead when not debugging

### Technical Choices

1. **Context Pattern**: Single context object manages state
2. **Caching**: File-level with mtime-based invalidation
3. **Event-Driven**: Debug events via callbacks
4. **FFI Boundary**: Clear separation of Simple API and Rust implementation
5. **Error Handling**: Result/Option types for safety

---

## Contributing

### Before Starting

1. Review this index
2. Read relevant guides
3. Check existing implementations
4. Understand FFI requirements

### Implementation Checklist

For LSP:
- [ ] Implement FFI functions
- [ ] Create SFFI spec
- [ ] Update LSP server
- [ ] Write tests
- [ ] Update documentation

For DAP:
- [ ] Implement FFI functions
- [ ] Modify interpreter for breakpoints
- [ ] Update DAP server
- [ ] Write tests
- [ ] Update documentation

For MCP:
- [ ] Design resource/prompt APIs
- [ ] Implement managers
- [ ] Update MCP server
- [ ] Write tests
- [ ] Update documentation

---

## Contact

For questions about this integration project:
- Review: [Phase 1 Completion Report](report/mcp_lsp_dap_phase1_completion_2026-02-04.md)
- Check: [Integration Analysis](research/mcp_lsp_dap_integration_analysis.md)
- See: Individual API guides

---

## Version History

| Version | Date | Changes |
|---------|------|---------|
| 1.0 | 2026-02-04 | Initial index created |
| | | Phase 1 APIs designed |
| | | Documentation complete |

---

**Last Updated**: 2026-02-04
**Next Review**: After Phase 2 completion
