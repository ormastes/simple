# Simple Language Version History

## Version 0.4.0 (2026-02-05) - Infrastructure Release

### Highlights
- **MCP Server Complete** - Model Context Protocol with full JSON-RPC 2.0 support
- **Unified Database Library** - Production-ready with atomic operations
- **Self-Hosting Build System** - Complete build pipeline in Simple
- **Pure Simple DL Library** - Tensor, autograd, neural network layers

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

### Statistics
- Simple files: 2,000+
- Simple lines: 190,000+
- Tests: 631+

---

## Version 0.5.0 (2026-02-08) - Pure Simple Release

### Achievements

#### 100% Pure Simple Architecture ✅
- [x] Rust source completely removed (24.2GB freed)
- [x] Pre-built runtime binary (33MB) — no Rust toolchain needed
- [x] Pure Simple parser (2,144 lines, fully self-hosting)
- [x] 1,109+ Simple source files, 190,000+ lines

#### Grammar Updates (3 Weeks) ✅
- [x] Parser: `async`, `await`, `spawn`, `actor`, `#[]` attributes
- [x] `with` statement (context managers) — `enter()` + `cleanup()` protocol
- [x] Set literals `s{1, 2, 3}` — full compiler pipeline
- [x] Async state machine generation and `Future<T>` HIR support
- [x] Async/await error diagnostics in HIR pipeline
- [x] Desugaring pass integrated into compilation pipeline

#### Cross-Platform CI & Release ✅
- [x] All CI workflows rewritten for pure Simple (no Rust)
- [x] Multi-platform bootstrap loader with auto-detection
- [x] 7 platform packages (Linux, macOS, Windows, FreeBSD × architectures)
- [x] FreeBSD support via Linuxulator
- [x] `-c` flag with full module resolution (temp file approach)

#### Production Infrastructure ✅
- [x] Unified Database Library (98/115 tests, 85.2%)
- [x] MCP Server — JSON-RPC 2.0 with pagination, structured output
- [x] Stdlib SFFI — 5 phases (String, Collections, Math, System, Path)
- [x] Static method desugaring (impl Type: static fn)
- [x] Script migration — 25/25 Python/Bash scripts → Simple
- [x] SDoctest — documentation testing (669 files, 4,963 blocks)

#### Test Suite ✅
- [x] 100% pass rate on all active tests
- [x] 3,606/4,379 broad lib tests passing (82%)
- [x] 458 spec files, 324 fully passing
- [x] Test suite repair (54+ files bulk-fixed)

### Known Issues (0.5.0)
- Runtime parser doesn't support `with` / `s{}` syntax yet (requires runtime rebuild)
- DL examples (`examples/pure_nn/`) need interpreter support for generic type static methods
- ~773 broad test failures remain (imported class constructors, closure capture, etc.)

### Statistics
- Simple files: 1,109+
- Simple lines: 190,000+
- Tests: 3,606+ passing
- Platforms: 7
- Rust source: 0 lines

---

## Version 0.6.0 (Planned) - Deep Learning Edition

### Planned Features

#### Deep Learning Examples & Library
- [ ] Fix module resolution for `lib.pure.*` imports in interpreter
- [ ] Verify all `examples/pure_nn/` examples run correctly
- [ ] GPU acceleration via SFFI (PyTorch/CUDA backend)
- [ ] Model serialization/deserialization
- [ ] Training loop utilities
- [ ] Comprehensive examples: XOR, regression, iris, MNIST

#### Runtime Rebuild
- [ ] Rebuild runtime with `with` statement and `s{}` parser support
- [ ] Enable 533+ blocked tests

#### Code Quality
- [ ] Lint rule expansion
- [ ] Auto-fix improvements
- [ ] Test coverage increase toward 90%+

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
- GitHub releases: `https://github.com/simple-lang/simple/releases`
