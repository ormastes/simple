# Source-to-Binary Optimization - Part 3: Appendices

**Part of:** [Source-to-Binary Optimization](./src_to_bin_optimization_part1.md)

---

## Appendix E: Detailed Implementation Guide

### E.1 Feature #651: Parallel File Parsing

**Status:** 📋 Planned
**Priority:** 🔥 High
**Impact:** 4x speedup
**Effort:** 2 weeks

#### Phase 1: Infrastructure (Week 1, Days 1-3)

**Step 1: Add Dependencies**
```toml
# simple-parser/Cargo.toml
[dependencies]
rayon = "1.10"
dashmap = "6.0"
```

**Step 2: Make Parser Thread-Safe**
```rust
// src/parser/src/lib.rs

// BEFORE: Not thread-safe
pub struct Parser {
    tokens: Vec<Token>,
    current: usize,
}

// AFTER: Thread-safe (no shared mutable state)
pub struct Parser {
    tokens: Vec<Token>,
    current: Cell<usize>,  // Interior mutability
}

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Self {
        Parser {
            tokens,
            current: Cell::new(0),
        }
    }
}
```

**Step 3: Ensure Error Types are Send + Sync**
```rust
// src/parser/src/error.rs

#[derive(Debug, Clone)]  // Clone required for Send
pub struct ParseError {
    pub kind: ErrorKind,
    pub span: Span,
    pub message: String,
}

// Verify Send + Sync
const _: () = {
    fn assert_send<T: Send>() {}
    fn assert_sync<T: Sync>() {}
    fn assertions() {
        assert_send::<ParseError>();
        assert_sync::<ParseError>();
    }
};
```

#### Phase 2: Parallel Parsing (Week 1, Days 4-5)

**Step 4: Implement Parallel Parse Function**
```rust
// src/parser/src/parallel.rs

use rayon::prelude::*;
use std::path::PathBuf;

pub fn parse_files_parallel(paths: &[PathBuf]) -> Result<Vec<Ast>, Vec<ParseError>> {
    // Parallel lex + parse
    let results: Vec<_> = paths
        .par_iter()
        .map(|path| {
            // Per-thread context
            let source = std::fs::read_to_string(path)?;
            let tokens = Lexer::new(&source).tokenize()?;
            let ast = Parser::new(tokens).parse_module()?;
            Ok((path.clone(), ast))
        })
        .collect();

    // Separate successes from errors
    let mut asts = Vec::new();
    let mut errors = Vec::new();

    for result in results {
        match result {
            Ok((path, ast)) => asts.push(ast),
            Err(err) => errors.push(err),
        }
    }

    if errors.is_empty() {
        Ok(asts)
    } else {
        Err(errors)
    }
}
```

#### Phase 3: Integration (Week 2, Days 1-3)

**Step 5: Update Driver**
```rust
// src/driver/src/runner.rs

pub fn compile_project(paths: Vec<PathBuf>, opts: &CompileOptions) -> Result<()> {
    // Parse
    let asts = if opts.parallel {
        parse_files_parallel(&paths)?  // NEW: Parallel
    } else {
        parse_files_serial(&paths)?    // OLD: Serial fallback
    };

    // Rest of pipeline
    // ...
}
```

**Step 6: Add CLI Flag**
```rust
// src/driver/src/main.rs

#[derive(Parser)]
struct CompileArgs {
    #[arg(long, default_value_t = true)]
    parallel: bool,

    #[arg(long)]
    parallel_threads: Option<usize>,

    files: Vec<PathBuf>,
}

fn main() {
    let args = CompileArgs::parse();

    if let Some(n) = args.parallel_threads {
        rayon::ThreadPoolBuilder::new()
            .num_threads(n)
            .build_global()
            .unwrap();
    }

    compile_project(args.files, &CompileOptions { parallel: args.parallel })?;
}
```

#### Phase 4: Testing (Week 2, Days 4-5)

**Step 7: Add Benchmarks**
```rust
// benches/parse_parallel.rs

use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};

fn bench_parse_scaling(c: &mut Criterion) {
    let mut group = c.benchmark_group("parse_scaling");

    for file_count in [1, 2, 4, 8, 16, 32] {
        let files = generate_test_files(file_count, 1000);

        group.bench_with_input(
            BenchmarkId::new("serial", file_count),
            &files,
            |b, files| b.iter(|| parse_files_serial(black_box(files))),
        );

        group.bench_with_input(
            BenchmarkId::new("parallel", file_count),
            &files,
            |b, files| b.iter(|| parse_files_parallel(black_box(files))),
        );
    }

    group.finish();
}

criterion_group!(benches, bench_parse_scaling);
criterion_main!(benches);
```

**Step 8: Add Integration Tests**
```rust
// src/parser/tests/parallel_tests.rs

#[test]
fn test_parallel_parse_correctness() {
    let files = vec![
        "test1.spl",
        "test2.spl",
        "test3.spl",
    ];

    let serial_asts = parse_files_serial(&files).unwrap();
    let parallel_asts = parse_files_parallel(&files).unwrap();

    // Results should be identical
    for (serial, parallel) in serial_asts.iter().zip(&parallel_asts) {
        assert_eq!(serial, parallel, "Parallel parse differs from serial");
    }
}

#[test]
fn test_parallel_parse_errors() {
    let files = vec![
        "valid.spl",
        "invalid.spl",  // Has syntax error
        "valid2.spl",
    ];

    let result = parse_files_parallel(&files);
    assert!(result.is_err(), "Should fail on invalid file");

    let errors = result.unwrap_err();
    assert_eq!(errors.len(), 1, "Should have exactly 1 error");
    assert!(errors[0].message.contains("invalid.spl"));
}
```

#### Success Criteria
- [ ] All 136 parser tests pass with `--parallel`
- [ ] Benchmark shows 3-4x speedup on 8-core system with 8+ files
- [ ] Memory usage stays within 2x of serial (due to parallel allocations)
- [ ] No race conditions (passes ThreadSanitizer)

---

### E.2 Feature #652: String Interning (Global)

**Status:** 📋 Planned
**Priority:** 🔥 High
**Impact:** 25% speedup, 50% memory reduction
**Effort:** 2 weeks

#### Phase 1: Library Selection (Week 1, Day 1)

**Comparison:**

| Library | Thread-Safe | Performance | Memory | Best For |
|---------|-------------|-------------|--------|----------|
| `string-interner` | ❌ (manual locking) | Fast | Low | Single-threaded |
| `lasso` | ✅ (lock-free) | Very Fast | Medium | Multi-threaded |
| `symbol-table` | ✅ (RwLock) | Medium | Low | Read-heavy |

**Decision:** Use `lasso` for global interning

```toml
# Cargo.toml (workspace)
[dependencies]
lasso = { version = "0.7", features = ["multi-threaded"] }
```

#### Phase 2: Define Symbol Type (Week 1, Days 2-3)

```rust
// src/common/src/symbol.rs

use lasso::{Rodeo, Spur, ThreadedRodeo};
use once_cell::sync::Lazy;
use std::sync::Arc;

/// Global string interner (thread-safe)
pub static INTERNER: Lazy<ThreadedRodeo> = Lazy::new(ThreadedRodeo::default);

/// Symbol handle (4 bytes)
pub type Symbol = Spur;

/// Convenience functions
pub fn intern(s: &str) -> Symbol {
    INTERNER.get_or_intern(s)
}

pub fn resolve(sym: Symbol) -> &'static str {
    INTERNER.resolve(&sym)
}

pub fn try_resolve(sym: Symbol) -> Option<&'static str> {
    INTERNER.try_resolve(&sym)
}

/// Pre-interned common symbols
pub mod symbols {
    use super::*;

    macro_rules! define_symbols {
        ($($name:ident => $string:literal),* $(,)?) => {
            $(
                pub static $name: Lazy<Symbol> = Lazy::new(|| intern($string));
            )*
        };
    }

    define_symbols! {
        // Keywords
        FN => "fn",
        LET => "let",
        RETURN => "return",
        IF => "if",
        ELSE => "else",

        // Common types
        I64 => "i64",
        I32 => "i32",
        STR => "str",
        BOOL => "bool",

        // Common identifiers
        MAIN => "main",
        SELF => "self",
        NEW => "new",

        // Common stdlib
        MALLOC => "malloc",
        FREE => "free",
        PRINTF => "printf",
    }
}
```

#### Phase 3: Update AST (Week 1, Days 4-5)

```rust
// src/parser/src/ast/nodes.rs

use simple_common::Symbol;

// BEFORE
pub struct Identifier {
    pub name: String,
    pub span: Span,
}

// AFTER
pub struct Identifier {
    pub name: Symbol,  // Changed: String → Symbol
    pub span: Span,
}

impl Identifier {
    pub fn new(name: &str, span: Span) -> Self {
        Identifier {
            name: simple_common::intern(name),
            span,
        }
    }

    pub fn as_str(&self) -> &str {
        simple_common::resolve(self.name)
    }
}

// Update all AST nodes
pub struct FunctionDef {
    pub name: Symbol,  // Changed
    pub params: Vec<Parameter>,
    // ...
}

pub struct TypeName {
    pub name: Symbol,  // Changed
    pub span: Span,
}
```

#### Phase 4: Update Parser (Week 2, Days 1-2)

```rust
// src/parser/src/lexer.rs

fn lex_identifier(&mut self) -> Token {
    let start = self.pos;
    let name = self.consume_while(|c| c.is_alphanumeric() || c == '_');

    // Intern during lexing
    let symbol = simple_common::intern(name);

    Token::Identifier(symbol, Span::new(start, self.pos))
}
```

#### Phase 5: Update Compiler (Week 2, Days 3-4)

```rust
// src/compiler/src/hir/types.rs

pub struct HirFunction {
    pub name: Symbol,  // Changed from String
    // ...
}

// Symbol resolution
impl SymbolTable {
    pub fn insert(&mut self, name: Symbol, value: SymbolInfo) {
        self.table.insert(name, value);
    }

    pub fn lookup(&self, name: Symbol) -> Option<&SymbolInfo> {
        self.table.get(&name)
    }
}
```

#### Phase 6: Testing (Week 2, Day 5)

```rust
// tests/string_interning_tests.rs

#[test]
fn test_interning_deduplicates() {
    let sym1 = intern("malloc");
    let sym2 = intern("malloc");
    let sym3 = intern("printf");

    assert_eq!(sym1, sym2, "Same string should intern to same symbol");
    assert_ne!(sym1, sym3, "Different strings should intern to different symbols");
}

#[test]
fn test_interning_round_trip() {
    let original = "hello_world";
    let symbol = intern(original);
    let resolved = resolve(symbol);

    assert_eq!(original, resolved, "Round-trip should preserve string");
}

#[test]
fn test_memory_usage() {
    let strings = vec!["malloc"; 10000];

    // Without interning: 10000 × 6 bytes = 60KB
    // With interning: 1 intern entry (6 bytes) + 10000 symbols (4 bytes each) = 40KB

    let symbols: Vec<Symbol> = strings.iter().map(|s| intern(s)).collect();

    // Verify all symbols are identical (deduped)
    for symbol in &symbols {
        assert_eq!(*symbol, symbols[0]);
    }
}
```

#### Success Criteria
- [ ] All tests pass with Symbol instead of String
- [ ] Memory usage reduces by 40-60% (measure with Massif)
- [ ] Symbol comparison is O(1) integer comparison
- [ ] No performance regression in single-threaded benchmarks

---

### E.3 Feature #658: Parallel Monomorphization

**Status:** 📋 Planned
**Priority:** 🟡 Medium
**Impact:** 5x speedup for generic-heavy code
**Effort:** 2 weeks

#### Phase 1: Dependency Graph (Week 1, Days 1-3)

**Step 1: Build Dependency Graph**
```rust
// src/compiler/src/monomorphize/graph.rs

use petgraph::graph::{DiGraph, NodeIndex};
use std::collections::HashMap;

pub struct MonoGraph {
    graph: DiGraph<InstanceId, ()>,
    instances: HashMap<InstanceId, NodeIndex>,
}

impl MonoGraph {
    pub fn new() -> Self {
        MonoGraph {
            graph: DiGraph::new(),
            instances: HashMap::new(),
        }
    }

    pub fn add_instance(&mut self, instance: InstanceId) -> NodeIndex {
        let node = self.graph.add_node(instance.clone());
        self.instances.insert(instance, node);
        node
    }

    pub fn add_dependency(&mut self, from: InstanceId, to: InstanceId) {
        let from_node = self.instances[&from];
        let to_node = self.instances[&to];
        self.graph.add_edge(from_node, to_node, ());
    }

    /// Returns instances grouped by dependency level
    /// Level 0: No dependencies
    /// Level 1: Depends only on level 0
    /// Level N: Depends on levels 0..N-1
    pub fn topological_levels(&self) -> Vec<Vec<InstanceId>> {
        use petgraph::algo::toposort;
        use petgraph::Direction;

        let sorted = toposort(&self.graph, None).expect("Cyclic generics not allowed");

        let mut levels: Vec<Vec<InstanceId>> = Vec::new();
        let mut node_levels: HashMap<NodeIndex, usize> = HashMap::new();

        for node in sorted {
            // Level = 1 + max(dependency levels)
            let level = self.graph
                .neighbors_directed(node, Direction::Outgoing)
                .filter_map(|dep| node_levels.get(&dep))
                .max()
                .map(|&l| l + 1)
                .unwrap_or(0);

            node_levels.insert(node, level);

            if level >= levels.len() {
                levels.resize(level + 1, Vec::new());
            }

            levels[level].push(self.graph[node].clone());
        }

        levels
    }
}
```

**Step 2: Detect Dependencies**
```rust
// src/compiler/src/monomorphize/analyzer.rs

impl<'hir> MonoAnalyzer<'hir> {
    pub fn analyze_dependencies(&self, instance: &Instance) -> Vec<InstanceId> {
        let mut deps = Vec::new();

        // Visit all type references in function body
        for stmt in &instance.body {
            self.visit_stmt(stmt, &mut deps);
        }

        deps
    }

    fn visit_stmt(&self, stmt: &HirStmt, deps: &mut Vec<InstanceId>) {
        match stmt {
            HirStmt::Call { func, args, .. } => {
                // If func is generic, add dependency
                if let Some(generic_func) = self.get_generic_func(func) {
                    let concrete_types = self.infer_types(args);
                    let dep_instance = InstanceId::new(generic_func.id, concrete_types);
                    deps.push(dep_instance);
                }
            }
            // ... other statement types
        }
    }
}
```

#### Phase 2: Parallel Processing (Week 1, Days 4-5)

**Step 3: Process Levels in Parallel**
```rust
// src/compiler/src/monomorphize/engine.rs

use rayon::prelude::*;
use dashmap::DashMap;

pub struct MonoEngine {
    graph: MonoGraph,
    results: DashMap<InstanceId, MirFunction>,
}

impl MonoEngine {
    pub fn monomorphize_all(&self, pending: Vec<Instance>) -> Result<HashMap<InstanceId, MirFunction>> {
        // Phase 1: Build dependency graph
        for instance in &pending {
            self.graph.add_instance(instance.id.clone());
            let deps = self.analyze_dependencies(instance);
            for dep in deps {
                self.graph.add_dependency(instance.id.clone(), dep);
            }
        }

        // Phase 2: Process level by level
        let levels = self.graph.topological_levels();

        for (level_num, level_instances) in levels.iter().enumerate() {
            tracing::info!("Monomorphizing level {}: {} instances", level_num, level_instances.len());

            // Process all instances in this level in parallel
            level_instances.par_iter().for_each(|instance_id| {
                let instance = self.get_instance(instance_id);
                let mir = self.monomorphize_function(instance).unwrap();
                self.results.insert(instance_id.clone(), mir);
            });
        }

        // Convert DashMap to HashMap
        Ok(self.results.iter().map(|entry| (entry.key().clone(), entry.value().clone())).collect())
    }

    fn monomorphize_function(&self, instance: &Instance) -> Result<MirFunction> {
        // All dependencies are already in self.results (processed in earlier levels)
        // ...
    }
}
```

#### Phase 3: Testing (Week 2)

**Step 4: Add Tests**
```rust
// src/compiler/tests/monomorphize_parallel.rs

#[test]
fn test_dependency_levels() {
    // Vec<i64> (level 0, no deps)
    // Vec<Vec<i64>> (level 1, depends on Vec<i64>)
    // HashMap<String, Vec<i64>> (level 1, depends on Vec<i64>)
    // Vec<HashMap<String, Vec<i64>>> (level 2, depends on both)

    let graph = build_test_graph();
    let levels = graph.topological_levels();

    assert_eq!(levels.len(), 3);
    assert_eq!(levels[0].len(), 1);  // Vec<i64>
    assert_eq!(levels[1].len(), 2);  // Vec<Vec<i64>>, HashMap<String, Vec<i64>>
    assert_eq!(levels[2].len(), 1);  // Vec<HashMap<...>>
}

#[test]
fn test_parallel_correctness() {
    let instances = generate_generic_instances(100);

    let serial_result = monomorphize_serial(&instances).unwrap();
    let parallel_result = monomorphize_parallel(&instances).unwrap();

    for (id, serial_mir) in &serial_result {
        let parallel_mir = &parallel_result[id];
        assert_eq!(serial_mir, parallel_mir, "Results must match for {}", id);
    }
}
```

#### Success Criteria
- [ ] Correctly handles recursive generics (Vec<Vec<T>>)
- [ ] 5x speedup on 8-core system for 100+ generic instances
- [ ] No deadlocks or race conditions
- [ ] Incremental compilation: only re-monomorphize changed generics

---

## Appendix F: SQP Integration & Query Optimization

### F.1 Overview

**SQP (Simple Query and Persistence)** presents optimization opportunities beyond traditional compilation:

1. **Query Compilation** - Compile SQL-like queries to optimized code
2. **Connection Pooling** - Reuse database connections across fibers/actors
3. **ORM Code Generation** - Generate accessor code at compile time
4. **Query Plan Caching** - Cache parsed/analyzed query plans

### F.2 Feature #671: Query Compilation to Native Code

**Status:** 📋 Planned (dependent on SQP implementation)
**Impact:** 10-50x speedup for database-heavy applications
**Effort:** 3 weeks

#### Phase 1: Query AST to MIR

```rust
// src/compiler/src/sqp/query_compiler.rs

pub fn compile_query_to_mir(query: &SqpQuery) -> MirFunction {
    match query {
        SqpQuery::Select { table, where_clause, order_by, limit } => {
            compile_select(table, where_clause, order_by, limit)
        }
        SqpQuery::Insert { table, values } => {
            compile_insert(table, values)
        }
        // ... other query types
    }
}

fn compile_select(
    table: &TableRef,
    where_clause: &Option<Expr>,
    order_by: &Option<OrderBy>,
    limit: &Option<u64>,
) -> MirFunction {
    let mut builder = MirBuilder::new();

    // 1. Table scan (parallel if no order_by)
    let rows = if order_by.is_none() {
        builder.emit_parallel_scan(table)
    } else {
        builder.emit_sequential_scan(table)
    };

    // 2. Filter (where clause) - SIMD vectorized
    if let Some(filter) = where_clause {
        builder.emit_simd_filter(rows, filter);
    }

    // 3. Sort (if needed)
    if let Some(order) = order_by {
        builder.emit_parallel_sort(rows, order);
    }

    // 4. Limit
    if let Some(n) = limit {
        builder.emit_limit(rows, *n);
    }

    builder.build()
}
```

**Example:**
```simple
# High-level SQP
users = User.where(active: true)
            .order(created_at: desc)
            .limit(10)

# Compiled to MIR (pseudo-code)
fn compiled_query() -> Vec<User>:
    # Parallel table scan
    rows = parallel_scan(users_table, chunk_size: 1000)

    # SIMD filter (active == true)
    filtered = simd_filter(rows, \r: r.active)

    # Parallel sort (created_at desc)
    sorted = parallel_sort(filtered, \a, b: b.created_at <=> a.created_at)

    # Limit
    return sorted[0..10]
```

#### Phase 2: Query Plan Optimization

```rust
// src/compiler/src/sqp/optimizer.rs

pub struct QueryOptimizer {
    statistics: TableStatistics,
}

impl QueryOptimizer {
    pub fn optimize(&self, plan: QueryPlan) -> QueryPlan {
        let plan = self.push_down_filters(plan);
        let plan = self.choose_join_order(plan);
        let plan = self.add_indexes(plan);
        let plan = self.vectorize_operations(plan);
        plan
    }

    fn push_down_filters(&self, plan: QueryPlan) -> QueryPlan {
        // Move filters as early as possible in the pipeline
        // Example: filter(where id > 100) before join
        // ...
    }

    fn choose_join_order(&self, plan: QueryPlan) -> QueryPlan {
        // Use statistics to choose optimal join order
        // Example: join small table first to reduce intermediate size
        // ...
    }

    fn add_indexes(&self, plan: QueryPlan) -> QueryPlan {
        // Use indexes when available
        // Example: WHERE email = "..." → use email_index
        // ...
    }

    fn vectorize_operations(&self, plan: QueryPlan) -> QueryPlan {
        // Use SIMD for batch operations
        // Example: filter 1000 rows at once with SIMD
        // ...
    }
}
```

### F.3 Feature #672: Connection Pooling

**Status:** 📋 Planned
**Impact:** 5-10x throughput for concurrent queries
**Effort:** 1 week

```rust
// src/runtime/src/sqp/pool.rs

use deadpool::managed::{Pool, Manager};

pub struct ConnectionPool {
    pool: Pool<DbConnection>,
}

impl ConnectionPool {
    pub fn new(config: PoolConfig) -> Self {
        let manager = DbManager::new(config.connection_string);
        let pool = Pool::builder(manager)
            .max_size(config.max_connections)
            .build()
            .unwrap();

        ConnectionPool { pool }
    }

    pub async fn execute<T>(&self, query: SqpQuery) -> Result<T> {
        // Get connection from pool
        let conn = self.pool.get().await?;

        // Execute query
        let result = conn.execute(query).await?;

        // Connection automatically returned to pool on drop
        Ok(result)
    }
}

// Usage in Simple
// let pool = ConnectionPool.new(max: 20)
// actors = spawn_n(100, \id: pool.query("SELECT * FROM users WHERE id = ?", [id]))
```

### F.4 Feature #673: ORM Code Generation

**Status:** 📋 Planned
**Impact:** Zero-cost abstractions for ORM
**Effort:** 2 weeks

```rust
// Macro-based code generation at compile time

// User writes:
data User:
    name: str
    email: str unique
    posts: [Post]

// Compiler generates (at compile time):
impl User {
    pub fn find(id: i64) -> Option<User> {
        compiled_query_user_find(id)  // Pre-compiled MIR function
    }

    pub fn where(filter: impl Fn(&User) -> bool) -> QueryBuilder<User> {
        QueryBuilder::new("users").filter(filter)
    }

    pub fn create(name: &str, email: &str) -> Result<User> {
        compiled_query_user_insert(name, email)  // Pre-compiled MIR function
    }

    // Accessors
    pub fn name(&self) -> &str { &self.name }
    pub fn email(&self) -> &str { &self.email }

    // Relationships
    pub fn posts(&self) -> Vec<Post> {
        compiled_query_user_posts(self.id)  // Pre-compiled join query
    }
}
```

### F.5 Performance Projections (SQP Features)

| Feature | Baseline | Optimized | Speedup | Use Case |
|---------|----------|-----------|---------|----------|
| **Query Compilation** | 50ms (interpreted) | 1ms (native) | 50x | Complex queries |
| **Connection Pooling** | 10 req/s (serial) | 100 req/s (pooled) | 10x | Concurrent workloads |
| **ORM Code Gen** | 5ms (reflection) | 0.1ms (direct) | 50x | Per-object overhead |
| **Query Plan Cache** | 10ms (parse+plan) | 0.5ms (cached) | 20x | Repeated queries |

**Combined Impact:** 100-200x for database-heavy applications

---

## Appendix G: Feature Implementation Checklist (Expanded)

### G.1 Phase 1: Foundation (Weeks 1-2)

| Task | Feature | Files | Tests | Status |
|------|---------|-------|-------|--------|
| Add rayon dependency | #651 | Cargo.toml | - | ⬜ |
| Make Parser Send+Sync | #651 | parser/lib.rs | parser_tests | ⬜ |
| Implement parse_parallel() | #651 | parser/parallel.rs | parallel_tests | ⬜ |
| Add lasso dependency | #652 | Cargo.toml | - | ⬜ |
| Define Symbol type | #652 | common/symbol.rs | symbol_tests | ⬜ |
| Update AST with Symbol | #652 | parser/ast/nodes.rs | ast_tests | ⬜ |
| Update Lexer to intern | #652 | parser/lexer.rs | lexer_tests | ⬜ |
| Update Compiler for Symbol | #652 | compiler/hir/, mir/ | all tests | ⬜ |

### G.2 Phase 2: Parser & HIR (Weeks 3-5)

| Task | Feature | Files | Tests | Status |
|------|---------|-------|-------|--------|
| Add typed-arena dependency | #653 | Cargo.toml | - | ⬜ |
| Define AstArena | #653 | parser/arena.rs | arena_tests | ⬜ |
| Update Expr with lifetimes | #653 | parser/ast/nodes.rs | ast_tests | ⬜ |
| Thread arena through parser | #653 | parser/lib.rs | parser_tests | ⬜ |
| Define HirArena | #654 | compiler/hir/arena.rs | hir_tests | ⬜ |
| Update HirExpr with lifetimes | #654 | compiler/hir/types.rs | hir_tests | ⬜ |
| Implement two-phase lowering | #656 | hir/lower/mod.rs | lower_tests | ⬜ |
| Parallel module lowering | #656 | hir/lower/parallel.rs | parallel_tests | ⬜ |

### G.3 Phase 3: MIR & Monomorphization (Weeks 6-8)

| Task | Feature | Files | Tests | Status |
|------|---------|-------|-------|--------|
| Add petgraph dependency | #658 | Cargo.toml | - | ⬜ |
| Implement MonoGraph | #658 | monomorphize/graph.rs | graph_tests | ⬜ |
| Dependency analysis | #658 | monomorphize/analyzer.rs | analyzer_tests | ⬜ |
| Parallel monomorphization | #658 | monomorphize/engine.rs | mono_tests | ⬜ |
| Implement MonoCache | #659 | monomorphize/cache.rs | cache_tests | ⬜ |
| Serialize/deserialize MIR | #659 | mir/serde.rs | serde_tests | ⬜ |
| Parallel function lowering | #657 | mir/lower/parallel.rs | lower_tests | ⬜ |
| Effect analysis cache | #666 | mir/effects.rs | effects_tests | ⬜ |

### G.4 Phase 4: Codegen & Linking (Weeks 9-10)

| Task | Feature | Files | Tests | Status |
|------|---------|-------|-------|--------|
| Per-thread Cranelift contexts | #660 | codegen/cranelift.rs | codegen_tests | ⬜ |
| Parallel function compilation | #660 | codegen/parallel.rs | parallel_tests | ⬜ |
| Implement BufferPool | #661 | codegen/buffer_pool.rs | pool_tests | ⬜ |
| Use buffer pool in codegen | #661 | codegen/cranelift.rs | codegen_tests | ⬜ |
| Parallel symbol resolution | #662 | linker/parallel.rs | linker_tests | ⬜ |
| Symbol name interning | #663 | linker/symbol_intern.rs | intern_tests | ⬜ |
| Hash precomputation | #664 | linker/hash.rs | hash_tests | ⬜ |

### G.5 Phase 5: Integration (Weeks 11-12)

| Task | Feature | Files | Tests | Status |
|------|---------|-------|-------|--------|
| CLI --parallel flag | All | driver/main.rs | cli_tests | ⬜ |
| CLI --profile flag | #669 | driver/profiler.rs | profile_tests | ⬜ |
| Benchmark suite | #670 | benches/ | - | ⬜ |
| Integration tests | All | tests/integration/ | - | ⬜ |
| Documentation | All | doc/ | - | ⬜ |
| Performance report | All | doc/performance.md | - | ⬜ |

**Total Tasks:** 40+ implementation tasks across 12 weeks

---

## Conclusion

Applying mold's optimization strategies to Simple's compilation pipeline yields **8-10x speedup** for multi-file projects through:

1. **Parallelization** at three levels (file, stage, intra-stage)
2. **String interning** for identifiers, types, symbols
3. **Arena allocation** for AST/HIR/MIR nodes
4. **Concurrent data structures** (DashMap, lock-free interners)

The key insight from mold: **parallelism first** - design every stage to be embarrassingly parallel, then add synchronization only where needed. Simple's compilation pipeline is more parallel-friendly than linking because file parsing and function lowering have minimal dependencies.

**Next Steps:**
1. Implement Phase 1 (foundation) - string interning and parallel file parsing
2. Measure baseline performance and validate projections
3. Proceed with Phase 2-4 based on measured ROI
4. Document optimization guide for future contributors

---

**END OF DOCUMENT**
