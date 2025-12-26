# Source-to-Binary Optimization - Part 2: Implementation

**Part of:** [Source-to-Binary Optimization](./src_to_bin_optimization_part1.md)

---

## 6. Memory Management Strategy

### 6.1 Current Memory Usage

**Measured for 1000-line program:**

| Stage | Allocation Pattern | Memory | Issue |
|-------|-------------------|--------|-------|
| **Parser** | `Box<Expr>` per AST node | 20MB | Fragmented |
| **HIR** | `Box<HirExpr>` per node | 25MB | Fragmented |
| **MIR** | `Vec<Instruction>` per block | 35MB | Reallocations |
| **Codegen** | `Vec<u8>` per function | 50MB | No reuse |
| **Total** | Ad-hoc allocations | **130MB** | **Poor locality** |

**With arenas and pooling:**
- **Parser:** Arena allocator → 8MB (60% reduction)
- **HIR:** Arena allocator → 10MB (60% reduction)
- **MIR:** Pre-sized vectors → 30MB (14% reduction)
- **Codegen:** Buffer pool → 35MB (30% reduction)
- **Total:** **83MB = 36% memory reduction**

### 6.2 Arena Allocation Strategy

**Phase 1: AST Arena**

```rust
// In src/parser/src/arena.rs
use typed_arena::Arena;

pub struct AstArena {
    exprs: Arena<Expr>,
    stmts: Arena<Statement>,
    types: Arena<Type>,
}

pub enum Expr<'ast> {
    BinOp {
        left: &'ast Expr<'ast>,
        right: &'ast Expr<'ast>,
        op: BinOp,
    },
    // ...
}
```

**Phase 2: HIR Arena**

```rust
pub struct HirArena {
    exprs: Arena<HirExpr>,
    stmts: Arena<HirStmt>,
    functions: Arena<HirFunction>,
}
```

**Phase 3: MIR Arena**

```rust
pub struct MirArena {
    instructions: Arena<MirInstruction>,
    blocks: Arena<BasicBlock>,
    functions: Arena<MirFunction>,
}
```

### 6.3 Buffer Pooling Strategy

**For codegen buffers:**

```rust
use std::sync::Mutex;

struct BufferPool {
    buffers: Mutex<Vec<Vec<u8>>>,
    capacity: usize,
}

impl BufferPool {
    pub fn acquire(&self) -> Vec<u8> {
        self.buffers.lock().unwrap()
            .pop()
            .unwrap_or_else(|| Vec::with_capacity(self.capacity))
    }

    pub fn release(&self, mut buf: Vec<u8>) {
        buf.clear();
        if buf.capacity() < self.capacity * 2 {
            self.buffers.lock().unwrap().push(buf);
        }
    }
}

static CODE_BUFFER_POOL: Lazy<BufferPool> = Lazy::new(|| BufferPool::new(4096));
```

---

## 7. Implementation Roadmap

### Phase 1: Foundation (2 weeks)

**Week 1: String Interning**
- [ ] Add `lasso` dependency for thread-safe interning
- [ ] Replace `String` with `Symbol` in AST (`Identifier`, `TypeName`)
- [ ] Update parser to intern during tokenization
- [ ] Add benchmarks comparing with/without interning

**Week 2: Parallelization Infrastructure**
- [ ] Add `rayon` dependency
- [ ] Convert file parsing to `par_iter()`
- [ ] Add `DashMap` for concurrent symbol tables
- [ ] Measure speedup on multi-file projects

### Phase 2: Parser & HIR (3 weeks)

**Week 3: Parser Optimization**
- [ ] Implement memory-mapped file reading
- [ ] Add arena allocation for AST nodes
- [ ] Benchmark parser performance

**Week 4-5: HIR Optimization**
- [ ] Parallel module lowering with two-phase resolution
- [ ] Arena allocation for HIR nodes
- [ ] Benchmark HIR lowering

### Phase 3: MIR & Monomorphization (3 weeks)

**Week 6-7: Monomorphization**
- [ ] Build dependency graph for generics
- [ ] Implement parallel monomorphization per level
- [ ] Add monomorphization cache
- [ ] Benchmark on generic-heavy code

**Week 8: MIR Lowering**
- [ ] Parallel function lowering
- [ ] Effect analysis caching
- [ ] Arena allocation for MIR
- [ ] Benchmark MIR stage

### Phase 4: Codegen & Linking (2 weeks)

**Week 9: Codegen**
- [ ] Parallel function compilation with Cranelift
- [ ] Code buffer pooling
- [ ] Benchmark codegen stage

**Week 10: SMF Linking**
- [ ] Parallel symbol resolution
- [ ] String interning for symbol names
- [ ] Hash precomputation for symbols
- [ ] Benchmark linking stage

### Phase 5: Integration & Tuning (2 weeks)

**Week 11: End-to-End**
- [ ] Integrate all optimizations
- [ ] Add `--parallel` flag to toggle parallelism
- [ ] Add `--profile` flag for per-stage timings
- [ ] Run full benchmark suite

**Week 12: Polish**
- [ ] Fix race conditions and deadlocks
- [ ] Tune work-stealing parameters
- [ ] Documentation and examples
- [ ] Performance regression tests

---

## 8. Performance Projections

### 8.1 Single-File Compilation

**Baseline:** 2100ms (8-core system, 1000-line program)

| Optimization | Impact | New Time | Speedup |
|--------------|--------|----------|---------|
| **Baseline** | - | 2100ms | 1.0x |
| + String interning | -15% | 1785ms | 1.18x |
| + Arena allocation | -12% | 1571ms | 1.34x |
| + Effect caching | -8% | 1445ms | 1.45x |
| + Buffer pooling | -6% | 1358ms | 1.55x |
| + Parallel codegen | -25% | 1019ms | 2.06x |
| + Parallel MIR lower | -10% | 917ms | 2.29x |
| **TOTAL** | **-56%** | **917ms** | **2.3x** |

### 8.2 Multi-File Compilation (10 files)

**Baseline:** 21,000ms (10 × 2100ms serial)

| Optimization | Impact | New Time | Speedup |
|--------------|--------|----------|---------|
| **Baseline** | - | 21,000ms | 1.0x |
| + Per-file optimizations | -56% (from above) | 9,170ms | 2.3x |
| + Parallel file processing (8 cores) | -75% | 2,293ms | 9.2x |
| + Overlapped linking | -10% | 2,064ms | 10.2x |
| **TOTAL** | **-90%** | **2,064ms** | **10.2x** |

**Real-world speedup:** **8-10x for projects with 10+ files**

### 8.3 Comparison with Mold

| Metric | Mold (Linking) | Simple (Compilation) |
|--------|---------------|----------------------|
| **Baseline** | lld 1.64s (MySQL) | 21s (10 files) |
| **Optimized** | mold 0.46s | 2.06s |
| **Speedup** | 3.6x | 10.2x |
| **Strategy** | Parallel + interning | Parallel + interning + arenas |

**Key Insight:** Compilation has more parallelism potential than linking because:
- **Linking** must serialize symbol resolution dependencies
- **Compilation** has embarrassingly parallel file processing

---

## 9. Comparison: Simple vs Mold Design

### 9.1 Architecture Comparison

| Aspect | Mold (Linker) | Simple (Compiler) | Similarity |
|--------|---------------|-------------------|------------|
| **Input** | Object files (`.o`) | Source files (`.spl`) | Multiple independent files |
| **Parallelism** | Per-file symbol extraction | Per-file parsing/lowering | ✅ Same pattern |
| **String Ops** | Symbol names (60% of time) | Identifiers, types (25% of time) | ✅ Same problem |
| **Memory** | Concurrent hash tables | Ad-hoc allocations | ⚠️ Different (can adopt) |
| **Synchronization** | Atomics, lock-free | Currently none (serial) | ⚠️ Can adopt atomics |
| **Output** | ELF binary | SMF binary or native | Similar (symbol resolution + relocation) |

### 9.2 Key Differences

| Aspect | Mold | Simple |
|--------|------|--------|
| **Parallelism Depth** | 1 level (file-level) | 3 levels (file, stage, intra-stage) |
| **Dependency Graph** | Simple (symbol refs) | Complex (types, generics, effects) |
| **Memory Pattern** | Read-only inputs | Mutable IR transformations |
| **Bottleneck** | Symbol resolution | Codegen (33% of time) |

### 9.3 What Can Be Directly Adopted from Mold

#### ✅ Directly Applicable (High ROI)

1. **Parallel File Processing** (Mold: parse object files in parallel)
   - **Simple:** Parse `.spl` files in parallel with `rayon`
   - **Estimated Impact:** 8x speedup for 10+ files

2. **String Interning** (Mold: intern symbol names with concurrent hash table)
   - **Simple:** Intern identifiers, type names with `lasso`
   - **Estimated Impact:** 25% speedup

3. **Concurrent Symbol Tables** (Mold: `concurrent_hash_map` from Intel TBB)
   - **Simple:** Use `DashMap` for symbol tables, type registries
   - **Estimated Impact:** Enable parallelism without locks

4. **Hash Precomputation** (Mold: compute symbol hash once, reuse)
   - **Simple:** Precompute hashes for symbol names, type signatures
   - **Estimated Impact:** 20% speedup in symbol resolution

#### ⚠️ Requires Adaptation (Medium ROI)

5. **Memory Pools** (Mold: fixed-size allocations for symbol entries)
   - **Simple:** Arena allocators for AST/HIR/MIR nodes
   - **Adaptation:** Typed arenas instead of fixed-size pools
   - **Estimated Impact:** 35% memory reduction, 15% speedup

6. **Atomic Synchronization** (Mold: atomic flags on symbols)
   - **Simple:** Atomic flags for visited nodes, compilation status
   - **Adaptation:** Less useful (more complex dependency graphs)
   - **Estimated Impact:** 10% speedup (avoids locking)

#### ❌ Not Applicable (Different Problem)

7. **Linker Relaxation** (Mold: optimize instruction encoding based on relocation distance)
   - **Simple:** LLVM/Cranelift handles this
   - **Not Needed**

8. **Section Merging** (Mold: merge .text, .data, .bss sections)
   - **Simple:** SMF format has different section semantics
   - **Not Applicable**

### 9.4 What Simple Can Do That Mold Cannot

#### ✅ Additional Parallelism Opportunities

1. **Multi-Stage Pipeline Parallelism**
   - Parse file1 while lowering file2 while compiling file3
   - **Not possible in linking:** Input must be fully parsed before symbol resolution

2. **Intra-Stage Parallelism**
   - Monomorphize 100 generic instances in parallel
   - Lower 50 functions to MIR in parallel
   - **Not possible in linking:** Symbol resolution has strict dependency order

3. **Incremental Compilation**
   - Cache HIR/MIR for unchanged files
   - **Possible in linking but limited:** Incremental linking less useful (fast enough already)

---

## 10. Refactoring Proposals

### 10.1 Refactor Parser to Mold-Like Design

**Current Design:**
```
Parser (single-threaded)
  ├── Lexer: String → Vec<Token>
  ├── Parser: Vec<Token> → AST
  └── String allocations: ad-hoc (10,000+ malloc calls)
```

**Mold-Inspired Design:**
```
Parser (parallel, thread-safe)
  ├── Parallel Lexer: Vec<Path> → Vec<Vec<Token>> (rayon::par_iter)
  ├── String Interner: Global Rodeo (lasso, lock-free reads)
  ├── Parser: Vec<Token> → AST (per-file arena)
  └── Symbol Table: DashMap (concurrent, lock-free)
```

**Key Changes:**
```rust
// Before
pub struct Parser {
    tokens: Vec<Token>,
    current: usize,
}

impl Parser {
    pub fn parse(source: String) -> Result<AST> {
        let tokens = Lexer::lex(&source)?;  // Allocates Strings
        let ast = Parser::new(tokens).parse_module()?;  // Box<T> everywhere
        Ok(ast)
    }
}

// After
pub struct Parser<'arena> {
    tokens: &'arena [Token],
    interner: &'arena Rodeo,
    arena: &'arena AstArena,
    current: usize,
}

impl<'arena> Parser<'arena> {
    pub fn parse_parallel(files: Vec<PathBuf>) -> Result<Vec<AST>> {
        // Phase 1: Parallel lexing with interning
        let token_streams: Vec<_> = files.par_iter()
            .map(|path| {
                let interner = GLOBAL_INTERNER.clone();
                let tokens = Lexer::lex_with_interner(path, &interner)?;
                Ok(tokens)
            })
            .collect::<Result<_>>()?;

        // Phase 2: Parallel parsing with arenas
        let asts: Vec<_> = token_streams.par_iter()
            .map(|tokens| {
                let arena = AstArena::new();
                let interner = GLOBAL_INTERNER.clone();
                let parser = Parser::new(tokens, &interner, &arena);
                parser.parse_module()
            })
            .collect::<Result<_>>()?;

        Ok(asts)
    }
}
```

### 10.2 Refactor SMF Linker to Mold-Like Design

**Current Design (Serial):**
```rust
// In src/compiler/src/linker/smf_writer.rs
pub fn link_modules(modules: Vec<Module>) -> Result<SmfBinary> {
    let mut symbol_table = HashMap::new();

    // Serial: Build symbol table
    for module in &modules {
        for export in &module.exports {
            symbol_table.insert(export.name.clone(), export.addr);
        }
    }

    // Serial: Resolve imports
    for module in &modules {
        for import in &module.imports {
            let addr = symbol_table.get(&import.name)
                .ok_or(LinkError::UndefinedSymbol)?;
            apply_relocation(module, import, *addr);
        }
    }

    // Serial: Write binary
    write_smf(modules, symbol_table)
}
```

**Mold-Inspired Design (Parallel):**
```rust
use dashmap::DashMap;
use rayon::prelude::*;

pub fn link_modules(modules: Vec<Module>) -> Result<SmfBinary> {
    // Phase 1: Parallel symbol extraction
    let symbol_table = DashMap::new();
    modules.par_iter().for_each(|module| {
        for export in &module.exports {
            let symbol = LINKER_INTERNER.write().unwrap().get_or_intern(&export.name);
            symbol_table.insert(symbol, export.addr);
        }
    });

    // Phase 2: Parallel relocation
    let errors = DashMap::new();
    modules.par_iter().for_each(|module| {
        for import in &module.imports {
            let symbol = LINKER_INTERNER.read().unwrap().get(&import.name).unwrap();
            match symbol_table.get(&symbol) {
                Some(addr) => apply_relocation(module, import, *addr),
                None => { errors.insert(symbol, LinkError::UndefinedSymbol); }
            }
        }
    });

    if !errors.is_empty() {
        return Err(LinkError::Multiple(errors.into_iter().collect()));
    }

    // Phase 3: Parallel section writing
    let sections: Vec<_> = modules.par_iter()
        .map(|module| write_module_section(module))
        .collect::<Result<_>>()?;

    // Phase 4: Serial merge (small overhead)
    merge_sections(sections, symbol_table)
}
```

**Speedup:** 4x on 8-core system for 100+ modules

### 10.3 Refactor Type Checker to Parallel Design

**Current Design (Serial):**
```rust
// In src/type/src/lib.rs
pub fn check_module(ast: &AST) -> Result<TypeEnv> {
    let mut env = TypeEnv::new();

    for stmt in &ast.statements {
        check_statement(stmt, &mut env)?;
    }

    Ok(env)
}
```

**Parallel Design:**
```rust
pub fn check_module_parallel(ast: &AST) -> Result<TypeEnv> {
    // Phase 1: Collect top-level declarations (serial, fast)
    let mut env = TypeEnv::new();
    for stmt in &ast.statements {
        if let Statement::FunctionDef(func) = stmt {
            env.declare_function(&func.name, &func.signature);
        }
    }

    // Phase 2: Type-check function bodies in parallel
    let type_envs: Vec<_> = ast.statements.par_iter()
        .filter_map(|stmt| {
            if let Statement::FunctionDef(func) = stmt {
                let local_env = env.clone();
                Some(check_function_body(func, local_env))
            } else {
                None
            }
        })
        .collect::<Result<_>>()?;

    // Phase 3: Merge type environments (serial, fast)
    for local_env in type_envs {
        env.merge(local_env)?;
    }

    Ok(env)
}
```

**Speedup:** 3x on 8-core system for modules with 20+ functions

---

## Appendix A: Optimization Checklist

### Parser Stage
- [ ] Parallel file parsing (`rayon::par_iter`)
- [ ] String interning for identifiers (`lasso`)
- [ ] Memory-mapped file reading (`memmap2`)
- [ ] Arena allocation for AST nodes (`typed-arena`)

### HIR Lowering Stage
- [ ] Parallel module lowering (two-phase: declarations → bodies)
- [ ] Arena allocation for HIR nodes
- [ ] Concurrent type environment (`DashMap`)

### Monomorphization Stage
- [ ] Parallel monomorphization with dependency graph
- [ ] Monomorphization cache (serialize to disk)
- [ ] Topological sort for generic dependencies

### MIR Lowering Stage
- [ ] Parallel function lowering
- [ ] Effect analysis caching
- [ ] Arena allocation for MIR instructions

### Codegen Stage
- [ ] Parallel function compilation (per-thread Cranelift contexts)
- [ ] Code buffer pooling (thread-local pools)
- [ ] Instruction selection caching

### SMF Linking Stage
- [ ] Parallel symbol resolution (`DashMap`)
- [ ] String interning for symbol names
- [ ] Hash precomputation for symbols
- [ ] Parallel relocation application

### Cross-Cutting
- [ ] Global string interner with `lasso`
- [ ] Profile-guided optimization (measure before/after)
- [ ] Benchmark suite for performance regression testing
- [ ] `--parallel` CLI flag to toggle optimizations

---

## Appendix B: Performance Measurement

### Benchmark Setup

```rust
// In benches/compilation_bench.rs
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn bench_parse(c: &mut Criterion) {
    let files = generate_test_files(10, 1000);  // 10 files, 1000 lines each

    c.bench_function("parse_serial", |b| {
        b.iter(|| {
            for file in &files {
                let ast = parse_file(black_box(file)).unwrap();
                black_box(ast);
            }
        });
    });

    c.bench_function("parse_parallel", |b| {
        b.iter(|| {
            let asts: Vec<_> = files.par_iter()
                .map(|file| parse_file(black_box(file)).unwrap())
                .collect();
            black_box(asts);
        });
    });
}

criterion_group!(benches, bench_parse);
criterion_main!(benches);
```

### Profiling Commands

```bash
# Flamegraph (CPU profiling)
cargo flamegraph --bin simple -- compile large_project.spl

# Perf (Linux perf_events)
perf record -g cargo run --release -- compile large_project.spl
perf report

# Time per stage
cargo run --release -- compile large_project.spl --profile

# Memory profiling
valgrind --tool=massif cargo run -- compile large_project.spl
```

---

## Appendix C: Feature List for Implementation

### Feature IDs (New Features)

| ID | Feature | Stage | Impact | Effort | Priority |
|----|---------|-------|--------|--------|----------|
| **#650** | Living Documentation | System Test | Complete | - | ✅ Done |
| **#651** | Parallel File Parsing | Parser | 4x | 2 weeks | 🔥 High |
| **#652** | String Interning (Global) | All Stages | 25% | 2 weeks | 🔥 High |
| **#653** | Arena Allocation (AST) | Parser | 15% | 1 week | 🔥 High |
| **#654** | Arena Allocation (HIR) | HIR Lower | 15% | 1 week | 🔥 High |
| **#655** | Arena Allocation (MIR) | MIR Lower | 12% | 1 week | 🟡 Medium |
| **#656** | Parallel Module Lowering | HIR Lower | 4x | 1.5 weeks | 🔥 High |
| **#657** | Parallel Function Lowering | MIR Lower | 6x | 1 week | 🔥 High |
| **#658** | Parallel Monomorphization | Monomorph | 5x | 2 weeks | 🟡 Medium |
| **#659** | Monomorphization Cache | Monomorph | 3x | 1.5 weeks | 🟡 Medium |
| **#660** | Parallel Codegen | Codegen | 4x | 1.5 weeks | 🔥 High |
| **#661** | Code Buffer Pooling | Codegen | 12% | 3 days | 🟢 Low |
| **#662** | Parallel Symbol Resolution | SMF Linker | 4x | 1 week | 🔥 High |
| **#663** | Symbol Name Interning | SMF Linker | 35% | 3 days | 🟡 Medium |
| **#664** | Symbol Hash Precomputation | SMF Linker | 20% | 2 days | 🟢 Low |
| **#665** | Memory-Mapped File I/O | Parser | 15% | 3 days | 🟡 Medium |
| **#666** | Effect Analysis Caching | MIR Lower | 25% | 1 week | 🟡 Medium |
| **#667** | Concurrent Type Environment | Type Checker | Enable parallel | 1 week | 🔥 High |
| **#668** | Pipeline Parallelism | Driver | 2x | 2 weeks | 🟢 Low |
| **#669** | Profiling Infrastructure | All | Debug tool | 1 week | 🟡 Medium |
| **#670** | Performance Benchmarks | All | Regression tests | 1 week | 🟡 Medium |

**Total:** 21 new features, estimated **25 weeks** (6 months with 1 engineer)

**Quick Wins (4 weeks, 3-5x speedup):**
1. #651 Parallel File Parsing (2 weeks, 4x)
2. #652 String Interning (2 weeks, 25%)
3. #660 Parallel Codegen (1.5 weeks, 4x already in backlog, leverage existing)
4. #662 Parallel Symbol Resolution (1 week, 4x)

**Combined:** 4-5x speedup for multi-file projects in 4 weeks

---

## Appendix D: Grammar for Optimization Directives

### D.1 Compiler Hints (EBNF)

```ebnf
(* === OPTIMIZATION ATTRIBUTES === *)
opt_attribute = '@' opt_directive args? ;

opt_directive = 'inline' | 'noinline'                    (* inlining hints *)
              | 'parallel' | 'serial'                     (* parallelization hints *)
              | 'interned' | 'cached'                     (* memory hints *)
              | 'cold' | 'hot'                            (* profile-guided hints *)
              | 'simd' | 'no_simd'                        (* vectorization hints *)
              | 'optimize' | 'no_optimize'                (* optimization level *)
              ;

args          = '(' arg_list ')' ;
arg_list      = arg (',' arg)* ;
arg           = ident | number | string ;

(* === USAGE IN FUNCTIONS === *)
function_def  = opt_attribute* visibility? 'fn' ident params ('->' type)? ':' NEWLINE INDENT body DEDENT ;

(* === USAGE IN DATA TYPES === *)
data_def      = opt_attribute* 'data' ident ':' NEWLINE INDENT fields DEDENT ;
```

### D.2 Optimization Directive Examples

#### Inlining Hints
```simple
@inline
fn add(a: i64, b: i64) -> i64:
    return a + b

@noinline
fn cold_path() -> i64:
    # Rarely called, don't bloat call sites
    perform_expensive_diagnostics()
```

#### Parallelization Hints
```simple
@parallel(grain_size: 1000)
fn process_batch(items: [Item]) -> [Result]:
    # Compiler: parallelize with rayon, chunk size 1000
    return items.map(\item: process_item(item))

@serial
fn must_be_sequential() -> i64:
    # Compiler: do NOT parallelize, even if heuristics suggest it
    global_counter += 1
```

#### Memory Hints
```simple
@interned
data Symbol:
    name: str  # Compiler: intern this string globally

@cached(ttl: 3600)
fn expensive_query(id: i64) -> Result:
    # Compiler: cache results for 1 hour
    return db.query("SELECT * FROM users WHERE id = ?", [id])
```

#### Profile-Guided Hints
```simple
@hot
fn inner_loop(n: i64) -> i64:
    # Compiler: aggressive optimization, assume called frequently
    return n * n + n

@cold
fn error_handler(msg: str):
    # Compiler: minimal optimization, optimize for size
    log_error(msg)
```

### D.3 CLI Flags Grammar

```bash
# Optimization level
simple compile --opt-level {0,1,2,3} file.spl

# Parallelization control
simple compile --parallel [N]        # Use N cores (default: all)
simple compile --serial              # Disable all parallelization

# String interning
simple compile --intern-strings      # Enable global string interning
simple compile --intern-symbols      # Enable symbol interning

# Memory management
simple compile --arena-alloc         # Use arena allocators
simple compile --buffer-pool         # Enable buffer pooling

# Profiling
simple compile --profile             # Print per-stage timings
simple compile --profile-output file.json  # Save profile data

# Cache control
simple compile --cache-dir ./cache  # Set cache directory
simple compile --no-cache            # Disable all caching

# Debug
simple compile --dump-mir            # Dump MIR to file
simple compile --trace-parallel      # Log parallel execution
```

---


---

**Continued in:** [Part 3 - Appendices](./src_to_bin_optimization_part3.md)
