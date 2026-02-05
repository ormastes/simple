# Simple Language Version History

## Version 0.4.0 (2026-02-05) - Pure Simple Release

### Highlights
- **100% Pure Simple Architecture** - All application code in Simple language
- **MCP Server Complete** - Model Context Protocol with full JSON-RPC 2.0 support
- **Unified Database Library** - Production-ready with atomic operations
- **Self-Hosting Build System** - Complete build pipeline in Simple

### Major Features

#### MCP (Model Context Protocol) Server
- Full JSON-RPC 2.0 over stdio implementation
- **Tools**: `read_code`, `list_files`, `search_code`, `file_info`
- **Resources**: `project://`, `file://`, `tree://`, `symbol://`, `type://`, `docs://`
- **Prompts**: 12 refactoring/generation templates
- CLI mode: `simple mcp read`, `simple mcp search`, `simple mcp expand`

#### Unified Database Library
- `StringInterner` - O(1) string deduplication
- `SdnTable`, `SdnRow`, `SdnDatabase` - Core types
- Atomic operations with file-based locking (2-hour stale lock detection)
- Query builder with fluent API (filters, sorting, limits)
- Domain databases: `BugDatabase`, `TestDatabase`, `FeatureDatabase`
- 27/27 core tests + 80+ integration tests passing

#### Pure Simple Deep Learning
- `src/lib/pure/` - Tensor, autograd, neural network layers
- `examples/pure_nn/` - XOR, regression, iris classification examples
- SFFI acceleration with PyTorch backend (optional)

#### Self-Hosting Build System
- 8 phases: Foundation, Testing, Coverage, Quality, Bootstrap, Package, Migration, Advanced
- 4,440 lines of implementation, 2,370 lines of tests (290+ SSpec tests)
- Commands: `build`, `test`, `coverage`, `lint`, `fmt`, `check`, `bootstrap`, `package`

### CLI Entry Point
- **Main CLI**: `bin/simple` (shell wrapper that calls Simple app)
- **Runtime**: `bin/simple_runtime` (internal, calls `src/app/cli/main.spl`)
- Usage: `simple <command>` or `simple <file.spl>`

### File Structure
```
bin/
├── simple              # Main CLI entry point
├── simple_runtime      # Runtime binary
└── bootstrap/          # Minimal bootstrap binaries

src/
├── app/                # Applications (CLI, build, MCP, LSP, etc.)
│   ├── cli/            # Main CLI dispatcher
│   ├── build/          # Self-hosting build system
│   ├── mcp/            # MCP server
│   ├── lsp/            # Language server
│   └── io/             # SFFI wrappers
├── lib/                # Libraries
│   ├── database/       # Unified database library
│   └── pure/           # Pure Simple DL library
├── std/                # Standard library
└── compiler/           # Compiler infrastructure
```

### Statistics
- Simple files: 2,000+
- Simple lines: 190,000+
- Tests: 631+

---

## Version 0.5.0 (Planned) - Grammar & DL Edition

### Planned Features

#### Grammar Refactoring
- [ ] Streamlined syntax for common patterns
- [ ] Improved error messages
- [ ] Parser performance optimization
- [ ] Better IDE support preparation

#### Deep Learning Enhancements
- [ ] Fix module resolution for `lib.pure.*` imports
- [ ] Verify all `examples/pure_nn/` examples run correctly
- [ ] GPU acceleration via SFFI
- [ ] Model serialization/deserialization
- [ ] Training loop utilities

### Known Issues (0.4.0)
- DL examples (`examples/pure_nn/`) have module import issues - `lib.pure.*` paths not resolving
- Some test specs have parse errors with newer syntax features

#### Documentation Updates
- [ ] Consistent file/directory references
- [ ] Updated architecture diagrams
- [ ] API reference generation
- [ ] Getting started guide refresh

#### Code Quality
- [ ] Lint rule expansion
- [ ] Auto-fix improvements
- [ ] Test coverage increase

---

## Previous Versions

### Version 0.3.x
- Initial self-hosting compiler
- Basic interpreter
- Core tooling

### Version 0.2.x
- Language design stabilization
- Type system implementation
- Pattern matching

### Version 0.1.x
- Initial language design
- Lexer/parser foundation
- Basic runtime

---

## Release Notes Location
- Full release notes: `release/RELEASE_NOTES_*.md`
- GitHub releases: `https://github.com/anthropics/simple/releases`
