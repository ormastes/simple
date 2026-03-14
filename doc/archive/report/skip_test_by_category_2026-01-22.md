# Skip Tests Detailed Breakdown by Category

Generated: 2026-01-22

## Parser & Tree-sitter (151 skips)

### Grammar Compilation (80 skips)
File: `test/lib/std/unit/parser/treesitter/grammar_simple_spec.spl`

**Core Grammar Rules:**
- Comments and documentation
- Module structure (imports, exports)
- Function definitions (parameters, return types)
- Struct and class declarations
- Enum and match expressions
- Type annotations and generics
- Expression parsing (binary, unary, literals)
- Statement parsing (let, return, if/else)

**Advanced Features:**
- Operator precedence
- Method calls and chaining
- Lambda expressions
- Pattern matching exhaustiveness
- Indentation-based blocks
- String interpolation
- Range expressions
- List/dict comprehensions

### Other Tree-sitter (71 skips)
- Grammar test framework integration
- Python grammar support
- Rust grammar support
- Language auto-detection
- Incremental parsing with edits
- Query system implementation
- Syntax highlighting queries
- Code folding ranges
- Error recovery strategies
- Parser optimization

## Concurrency (30 skips)

File: `test/lib/std/unit/concurrency/promise_spec.spl`

All blocked on: **Async runtime not implemented**

### Promise Creation
- Resolved promises
- Rejected promises
- Promise with executor
- Executor error handling

### Promise Operations
- then() chaining
- map() transformation
- flat_map() for nested promises
- catch() error handling
- finally() cleanup

### Promise Combinators
- Promise.all() - wait for all
- Promise.race() - first to complete
- Promise.all_settled() - wait for all results
- Empty promise handling

### Promise Invariants
- Resolve only once
- Reject only once
- Cannot resolve after reject
- Cannot reject after resolve

### Type Safety
- Type preservation through then()
- Type preservation through map()
- Generic promise lists
- Async function return types

## Debug Adapter Protocol (37 skips)

### DAP Server (15 skips)
File: `test/lib/std/unit/dap/server_spec.spl`
- Server initialization
- Breakpoint management
- Thread inspection
- Stack trace retrieval
- Variable inspection
- Expression evaluation
- Step commands (in, out, over)
- Continue/pause execution

### DAP Protocol (13 skips)
File: `test/lib/std/unit/dap/protocol_spec.spl`
- Initialize request/response
- Launch/attach requests
- Breakpoint requests
- Stack trace requests
- Scope/variable requests
- Evaluate requests
- Step/continue requests
- Disconnect handling

### DAP Types (9 skips)
- Source references
- Breakpoint locations
- Stack frames
- Scopes and variables
- Thread info
- Capabilities negotiation

## ML/Torch (42 skips)

### Tensor Operations (36 skips)
File: `test/lib/std/unit/ml/torch/tensor_spec.spl`
- Tensor creation (zeros, ones, rand)
- Shape operations (reshape, view, transpose)
- Math operations (add, mul, matmul)
- Reduction operations (sum, mean, max)
- Indexing and slicing
- Broadcasting rules
- Device management (CPU/GPU)
- Dtype conversions
- Gradient computation

### Neural Networks (6 skips)
File: `test/lib/std/unit/ml/nn/module_spec.spl`
- Module base class
- Layer composition
- Parameter registration
- Forward pass
- Training mode
- Evaluation mode

## Tooling (28 skips)

File: `test/lib/std/unit/tooling/tooling_spec.spl`

### Build System
- Build configuration
- Dependency resolution
- Incremental compilation
- Build caching
- Parallel builds

### Package Management
- Package manifest
- Dependency versions
- Lock files
- Package registry
- Local packages

### Code Generation
- Template processing
- Type-safe code gen
- FFI bindings
- Protocol buffers

### Project Management
- Project scaffolding
- Configuration files
- Migration tools
- Version management

## SDN Format (28 skips)

### Parser (15 skips)
Files: `test/lib/std/unit/sdn/parser_spec.spl`, `test/lib/std/system/sdn/file_io_spec.spl`
- Key-value pairs
- Inline dicts
- Inline arrays
- Block dicts
- Block arrays
- Named tables
- Typed tables
- Nested structures
- Syntax error reporting

### Compatibility (9 skips)
File: `test/lib/std/unit/sdn/compatibility_spec.spl`
- Match Rust for primitives (int, float, string, bool)
- Match Rust for collections (dicts, arrays)
- Compatible SDN output
- Compatible JSON output

### Roundtrip (7 skips)
File: `test/lib/std/unit/sdn/roundtrip_spec.spl`
- Preserve primitives
- Preserve inline/block collections
- Preserve nested structures
- Preserve tables

## Verification (26 skips)

File: `test/lib/std/unit/verification/memory_capabilities_spec.spl`

### Memory Safety
- Immutable reference capabilities
- Mutable reference capabilities
- Isolated reference capabilities
- Capability transitions
- Aliasing restrictions

### Type System Proofs
- Generic variance
- Subtyping relations
- Type soundness
- Effect system

### Runtime Properties
- No data races
- No use-after-free
- No null pointer dereferences
- Sequential consistency

## LSP (25 skips)

### Completions (8 skips)
- Context-aware completions
- Import completions
- Method completions
- Snippet expansions

### Diagnostics (7 skips)
- Syntax errors
- Type errors
- Warning levels
- Error recovery

### Navigation (6 skips)
- Go to definition
- Find references
- Document symbols
- Workspace symbols

### Code Actions (4 skips)
- Quick fixes
- Refactorings
- Organize imports
- Extract variable/function

## Testing Framework (79 skips)

### Contract Testing (22 skips)
File: `simple/std_lib/test/unit/testing/contract_spec.spl`
- Pre/post conditions
- Invariants
- Contract inheritance
- Runtime checking
- Contract documentation

### Property Testing (53 skips)
Files: Property generators, shrinking, runner
- Random generators
- Shrinking algorithms
- Property combinators
- Test case generation
- Failure minimization

### Snapshot Testing (52 skips)
Files: Snapshot formats, comparison, runner, basic
- Snapshot storage formats
- Diff algorithms
- Visual diffs
- Snapshot updates
- Multi-format snapshots

## Game Engine (20 skips)

### Physics (5 skips in collision)
- AABB collision detection
- Spatial hashing
- Collision manifolds
- Contact resolution

### Rendering (planned)
- Sprite batching
- Camera systems
- Particle effects
- Shader compilation

### Entity-Component System (planned)
- Component storage
- System scheduling
- Entity queries
- Archetype optimization

## Integration Tests (54 skips)

### UI/TUI (24 skips)
File: `test/lib/std/integration/ui/tui/ratatui_backend_spec.spl`
- Terminal backend
- Widget rendering
- Event handling
- Layout system

### ML Integration (16 skips)
File: `test/lib/std/integration/ml/simple_math_integration_spec.spl`
- End-to-end tensor ops
- Model training
- Data loading
- Inference pipeline

### Spec Framework (14 skips)
Files: `test/integration/spec/*_spec.spl`
- Formatter integration
- Runner integration
- Reporter integration

## System/Feature Tests (293 skips)

### Architecture (27 skips)
File: `test/lib/std/system/spec/arch_spec.spl`
- Module boundaries
- Dependency rules
- Layering constraints

### Stdlib Improvements (25 skips)
File: `test/lib/std/system/improvements/stdlib_improvements_spec.spl`
- API enhancements
- Performance optimizations
- New data structures

### Property Testing (53 skips)
- Generators for all types
- Shrinking strategies
- Custom properties

### Snapshot Testing (52 skips)
- Format support
- Comparison algorithms
- Update workflows

### SDN System (30 skips)
- CLI tools
- File I/O
- Schema validation

## Summary Statistics

| Category | Skips | % of Total |
|----------|-------|------------|
| Parser/Tree-sitter | 151 | 19.6% |
| System/Feature | 293 | 38.0% |
| Testing Framework | 79 | 10.2% |
| ML/Torch | 42 | 5.4% |
| DAP | 37 | 4.8% |
| Concurrency | 30 | 3.9% |
| Tooling | 28 | 3.6% |
| SDN | 28 | 3.6% |
| Verification | 26 | 3.4% |
| LSP | 25 | 3.2% |
| Game Engine | 20 | 2.6% |
| Integration | 54 | 7.0% |
| Other | 59 | 7.6% |
| **Total** | **772** | **100%** |

## Critical Path Analysis

**To unlock the most tests, prioritize:**

1. **Async Runtime** → Unblocks 30 concurrency tests
2. **Tree-sitter Grammar** → Unblocks 151 parser tests
3. **Testing Infrastructure** → Unblocks 79 testing framework tests
4. **DAP Implementation** → Unblocks 37 debug tests
5. **SDN Parser** → Unblocks 28 data format tests

**Total impact: 325 tests (42% of all skips)**
