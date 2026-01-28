# Shared Type Inference Architecture

## Executive Summary

This document describes the architecture for making the interpreter type inference module shareable and enabling the loader and linker to use inference for instantiating obj/binary during load and linking time.

**Goal**: Compile, loading, and interpreter type inference levels should be the same - minimal or no explicit type annotations needed.

**Implementation Principle**: Implement in Simple unless performance-critical (per CLAUDE.md).

**Key Components**:
1. **Shared Type Inference Module** - Simple implementation (`simple/compiler/inference/`)
2. **ObjTaker** - Simple implementation for object extraction and instantiation
3. **SMF Reader/Writer** - Shared between loader and linker (Rust for binary parsing, Simple for logic)
4. **Mold Linker Backend** - Rust FFI wrapper, Simple orchestration

---

## Architecture Overview

### Language Split

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        IMPLEMENTATION LANGUAGES                         │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  ┌─────────────────────────────────────────┐                           │
│  │           SIMPLE (.spl)                  │                           │
│  │  (Primary - all logic and algorithms)    │                           │
│  │                                          │                           │
│  │  - Type inference engine                 │                           │
│  │  - Unification algorithm                 │                           │
│  │  - Constraint solving                    │                           │
│  │  - ObjTaker logic                        │                           │
│  │  - Linker orchestration                  │                           │
│  │  - SDN parsing/writing                   │                           │
│  │  - Template instantiation                │                           │
│  └─────────────────────────────────────────┘                           │
│                                                                         │
│  ┌─────────────────────────────────────────┐                           │
│  │           RUST (FFI only)                │                           │
│  │  (Performance-critical binary ops)       │                           │
│  │                                          │                           │
│  │  - SMF binary read/write                 │                           │
│  │  - ELF/Mach-O generation                 │                           │
│  │  - mold subprocess execution             │                           │
│  │  - Memory-mapped file I/O                │                           │
│  └─────────────────────────────────────────┘                           │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### Component Layout

```
simple/
├── compiler/
│   ├── inference/                    # NEW: Shared type inference
│   │   ├── __init__.spl             # Module exports
│   │   ├── types.spl                # Type representation
│   │   ├── unify.spl                # Unification algorithm
│   │   ├── infer.spl                # Inference engine
│   │   ├── constraints.spl          # Constraint generation/solving
│   │   ├── deferred.spl             # Deferred hints for link-time
│   │   └── serialize.spl            # SDN serialization
│   │
│   ├── linker/                       # NEW: Simple linker
│   │   ├── __init__.spl             # Module exports
│   │   ├── obj_taker.spl            # Shared object extraction
│   │   ├── smf_reader.spl           # SMF reading (uses Rust FFI)
│   │   ├── smf_writer.spl           # SMF writing (uses Rust FFI)
│   │   ├── link.spl                 # Link pipeline
│   │   └── mold.spl                 # Mold backend wrapper
│   │
│   └── loader/                       # NEW: Simple loader
│       ├── __init__.spl             # Module exports
│       ├── module_loader.spl        # Module loading
│       └── instantiate.spl          # Generic instantiation

src/rust/
├── loader/src/
│   └── smf/                          # EXISTING: Keep binary SMF parsing
│       ├── header.rs                # Binary header read/write
│       ├── section.rs               # Section parsing
│       └── symbol.rs                # Symbol table
│
└── compiler/src/
    └── linker/
        └── mold_ffi.rs              # NEW: Rust FFI for mold execution
```

---

## Component Design

### 1. Shared Type Inference Module (Simple)

**Location**: `simple/compiler/inference/`

#### 1.1 Type Representation

```simple
# simple/compiler/inference/types.spl

enum Type:
    # Primitives
    Int(bits: i32, signed: bool)
    Float(bits: i32)
    Bool
    Str
    Nil

    # Inference-related
    Var(id: TypeVarId)                # Unresolved type variable
    Skolem(id: SkolemId)              # Rigid type variable

    # Compound types
    Function(params: List<Type>, ret: Type)
    Array(elem: Type, size: Option<i64>)
    Tuple(elements: List<Type>)
    Optional(inner: Type)

    # User-defined
    Struct(name: text, fields: List<Field>, type_params: List<Type>)
    Enum(name: text, variants: List<Variant>, type_params: List<Type>)
    Class(name: text, type_params: List<Type>)

    # Generic
    Generic(base: text, args: List<Type>)
    TypeParam(name: text)             # Uninstantiated parameter

    # Deferred (for link-time inference)
    Deferred(id: DeferredTypeId, constraints: List<Constraint>, fallback: Option<Type>)

struct TypeVarId:
    id: i64

struct DeferredTypeId:
    id: i64

struct Field:
    name: text
    ty: Type
```

#### 1.2 Unification Algorithm

```simple
# simple/compiler/inference/unify.spl

class Unifier:
    substitutions: Dict<TypeVarId, Type>
    next_var: i64

    static fn empty() -> Unifier:
        Unifier(substitutions: {}, next_var: 0)

    fn fresh_var() -> Type:
        val id = TypeVarId(id: self.next_var)
        self.next_var = self.next_var + 1
        Type.Var(id: id)

    fn unify(t1: Type, t2: Type) -> Result<(), UnifyError>:
        val t1 = self.resolve(t1)
        val t2 = self.resolve(t2)

        match (t1, t2):
            (Type.Var(id1), Type.Var(id2)) if id1 == id2:
                Ok(())

            (Type.Var(id), t) | (t, Type.Var(id)):
                if self.occurs_check(id, t):
                    Err(UnifyError.InfiniteType(id, t))
                else:
                    self.substitutions[id] = t
                    Ok(())

            (Type.Function(p1, r1), Type.Function(p2, r2)):
                if p1.len() != p2.len():
                    Err(UnifyError.ArityMismatch(p1.len(), p2.len()))
                else:
                    for (a, b) in p1.zip(p2):
                        self.unify(a, b)?
                    self.unify(r1, r2)

            (Type.Array(e1, _), Type.Array(e2, _)):
                self.unify(e1, e2)

            (Type.Generic(n1, a1), Type.Generic(n2, a2)) if n1 == n2:
                if a1.len() != a2.len():
                    Err(UnifyError.ArityMismatch(a1.len(), a2.len()))
                else:
                    for (a, b) in a1.zip(a2):
                        self.unify(a, b)?
                    Ok(())

            (t1, t2) if t1 == t2:
                Ok(())

            _:
                Err(UnifyError.CannotUnify(t1, t2))

    fn resolve(ty: Type) -> Type:
        match ty:
            Type.Var(id):
                match self.substitutions.get(id):
                    Some(t) -> self.resolve(t)
                    None -> ty
            _ -> ty

    fn occurs_check(id: TypeVarId, ty: Type) -> bool:
        match self.resolve(ty):
            Type.Var(other_id) -> id == other_id
            Type.Function(params, ret) ->
                params.any(\p: self.occurs_check(id, p)) or self.occurs_check(id, ret)
            Type.Array(elem, _) -> self.occurs_check(id, elem)
            Type.Generic(_, args) -> args.any(\a: self.occurs_check(id, a))
            _ -> false
```

#### 1.3 Inference Engine

```simple
# simple/compiler/inference/infer.spl

class InferenceEngine:
    unifier: Unifier
    env: TypeEnv
    deferred: List<DeferredHint>

    static fn create() -> InferenceEngine:
        InferenceEngine(
            unifier: Unifier.empty(),
            env: TypeEnv.empty(),
            deferred: []
        )

    fn infer_expr(expr: Expr) -> Result<Type, InferError>:
        match expr:
            Expr.Literal(lit) -> self.infer_literal(lit)
            Expr.Identifier(name) -> self.lookup(name)
            Expr.Call(callee, args) -> self.infer_call(callee, args)
            Expr.Lambda(params, body) -> self.infer_lambda(params, body)
            Expr.Binary(op, left, right) -> self.infer_binary(op, left, right)
            Expr.Array(elements) -> self.infer_array(elements)
            Expr.Access(obj, field) -> self.infer_access(obj, field)
            _ -> Ok(self.unifier.fresh_var())  # Defer unknown

    fn infer_literal(lit: Literal) -> Result<Type, InferError>:
        match lit:
            Literal.Int(_) -> Ok(Type.Int(bits: 64, signed: true))
            Literal.Float(_) -> Ok(Type.Float(bits: 64))
            Literal.String(_) -> Ok(Type.Str)
            Literal.Bool(_) -> Ok(Type.Bool)
            Literal.Nil -> Ok(Type.Nil)

    fn infer_call(callee: Expr, args: List<Expr>) -> Result<Type, InferError>:
        val callee_ty = self.infer_expr(callee)?
        val arg_types = args.map(\a: self.infer_expr(a)?)?

        val ret_ty = self.unifier.fresh_var()
        val expected_fn = Type.Function(params: arg_types, ret: ret_ty)

        self.unifier.unify(callee_ty, expected_fn)?
        Ok(self.unifier.resolve(ret_ty))

    fn infer_lambda(params: List<Param>, body: Expr) -> Result<Type, InferError>:
        val param_types = params.map(\p:
            match p.ty:
                Some(t) -> t
                None -> self.unifier.fresh_var()
        )

        # Extend environment
        self.env.push_scope()
        for (param, ty) in params.zip(param_types):
            self.env.bind(param.name, ty)

        val body_ty = self.infer_expr(body)?
        self.env.pop_scope()

        Ok(Type.Function(params: param_types, ret: body_ty))

    fn generate_deferred_hints() -> List<DeferredHint>:
        # Collect all unresolved type variables with their constraints
        self.deferred.filter(\h: not self.is_resolved(h.type_var))

    fn lookup(name: text) -> Result<Type, InferError>:
        self.env.lookup(name)
            .ok_or(InferError.Undefined(name))
```

### 2. ObjTaker (Simple)

**Location**: `simple/compiler/linker/obj_taker.spl`

```simple
# simple/compiler/linker/obj_taker.spl

class ObjTaker:
    inference: InferenceEngine
    template_cache: Dict<text, Template>
    instance_cache: Dict<text, ResolvedObject>
    smf_reader: SmfReader  # Uses Rust FFI

    static fn create(smf_reader: SmfReader) -> ObjTaker:
        ObjTaker(
            inference: InferenceEngine.create(),
            template_cache: {},
            instance_cache: {},
            smf_reader: smf_reader
        )

    fn take_object(symbol_name: text) -> Result<ResolvedObject, ObjTakeError>:
        # Check instance cache first
        if self.instance_cache.contains(symbol_name):
            return Ok(self.instance_cache[symbol_name])

        # Find symbol in SMF
        val symbol = self.smf_reader.lookup_symbol(symbol_name)?

        # Route based on symbol type
        if symbol.is_generic_template():
            self.take_generic(symbol)
        else if symbol.has_deferred_types():
            self.take_deferred(symbol)
        else:
            self.take_concrete(symbol)

    fn take_generic(symbol: SmfSymbol) -> Result<ResolvedObject, ObjTakeError>:
        # 1. Load template (or get from cache)
        val template = self.load_template(symbol)?

        # 2. Get usage hints from note.sdn
        val hints = self.smf_reader.get_inference_hints(symbol.name)?

        # 3. Infer type arguments from usage context
        val type_args = self.infer_type_args(template, hints)?

        # 4. Instantiate template
        val instance = self.instantiate(template, type_args)?

        # 5. Cache and return
        val mangled = self.mangle_name(symbol.name, type_args)
        self.instance_cache[mangled] = instance
        Ok(instance)

    fn take_deferred(symbol: SmfSymbol) -> Result<ResolvedObject, ObjTakeError>:
        # 1. Get deferred hints
        val hints = self.smf_reader.get_deferred_hints(symbol.name)?

        # 2. Build context from linked modules
        val context = self.build_link_context()?

        # 3. Apply deferred inference
        val resolved_types = self.inference.apply_deferred(hints, context)?

        # 4. Patch object with resolved types
        self.patch_object(symbol, resolved_types)

    fn take_concrete(symbol: SmfSymbol) -> Result<ResolvedObject, ObjTakeError>:
        # Direct extraction - no inference needed
        val code = self.smf_reader.read_code(symbol)?
        Ok(ResolvedObject.Code(bytes: code, symbol: symbol))

    fn load_template(symbol: SmfSymbol) -> Result<Template, ObjTakeError>:
        if self.template_cache.contains(symbol.name):
            return Ok(self.template_cache[symbol.name])

        val template_bytes = self.smf_reader.read_template_section(symbol)?
        val template = Template.deserialize(template_bytes)?

        self.template_cache[symbol.name] = template
        Ok(template)

    fn infer_type_args(template: Template, hints: InferenceHints) -> Result<List<Type>, ObjTakeError>:
        # Use inference engine to determine type arguments
        for hint in hints.usage_sites:
            self.inference.add_constraint(hint.constraint)

        val resolved = template.type_params.map(\param:
            self.inference.resolve_param(param)
        )

        # Check all params are resolved
        if resolved.any(\t: t.is_unresolved()):
            Err(ObjTakeError.CannotInferTypes(template.name))
        else:
            Ok(resolved)

    fn instantiate(template: Template, type_args: List<Type>) -> Result<ResolvedObject, ObjTakeError>:
        # Substitute type parameters with concrete types
        val substituted = template.substitute(type_args)

        # Generate code for instantiation
        val code = self.generate_code(substituted)?

        Ok(ResolvedObject.Code(bytes: code, symbol: substituted.symbol))

    fn mangle_name(base: text, type_args: List<Type>) -> text:
        val args_str = type_args.map(\t: t.mangle()).join("_")
        "{base}${args_str}"
```

### 3. SMF Reader/Writer (Hybrid)

**Simple layer**: `simple/compiler/linker/smf_reader.spl`
**Rust FFI**: `src/rust/loader/src/smf/` (existing)

```simple
# simple/compiler/linker/smf_reader.spl

extern class SmfReaderFfi:
    # Rust FFI for binary operations
    static fn open(path: text) -> Result<SmfReaderFfi, SmfError>
    fn read_header() -> SmfHeader
    fn read_section(index: i32) -> bytes
    fn read_symbol_table() -> List<SmfSymbolRaw>
    fn close()

class SmfReader:
    ffi: SmfReaderFfi
    header: SmfHeader
    symbols: Dict<text, SmfSymbol>
    inference_hints: Option<InferenceHints>

    static fn open(path: text) -> Result<SmfReader, SmfError>:
        val ffi = SmfReaderFfi.open(path)?
        val header = ffi.read_header()

        # Parse symbols into Simple structures
        val raw_symbols = ffi.read_symbol_table()
        val symbols = raw_symbols.map(\s: SmfSymbol.from_raw(s))
            .to_dict(\s: (s.name, s))

        # Load inference hints if present
        val inference_hints = if header.has_inference_hints():
            val section = ffi.read_section(header.inference_hints_index)
            Some(InferenceHints.parse(section))
        else:
            None

        Ok(SmfReader(
            ffi: ffi,
            header: header,
            symbols: symbols,
            inference_hints: inference_hints
        ))

    fn lookup_symbol(name: text) -> Result<SmfSymbol, SmfError>:
        self.symbols.get(name)
            .ok_or(SmfError.SymbolNotFound(name))

    fn get_inference_hints(symbol_name: text) -> Result<InferenceHints, SmfError>:
        self.inference_hints
            .and_then(\h: h.for_symbol(symbol_name))
            .ok_or(SmfError.NoHints(symbol_name))

    fn read_code(symbol: SmfSymbol) -> Result<bytes, SmfError>:
        val section = self.ffi.read_section(symbol.section_index)
        Ok(section[symbol.offset..symbol.offset + symbol.size])

    fn read_template_section(symbol: SmfSymbol) -> Result<bytes, SmfError>:
        if not symbol.is_generic_template():
            return Err(SmfError.NotTemplate(symbol.name))

        val section = self.ffi.read_section(self.header.template_code_index)
        Ok(section[symbol.template_offset..])
```

### 4. Linker (Simple with Mold Backend)

```simple
# simple/compiler/linker/link.spl

class Linker:
    obj_taker: ObjTaker
    output_symbols: List<ResolvedSymbol>
    unresolved: List<text>

    static fn create() -> Linker:
        Linker(
            obj_taker: None,  # Set per link job
            output_symbols: [],
            unresolved: []
        )

    fn link(inputs: List<text>, output: text, config: LinkConfig) -> Result<(), LinkError>:
        # 1. Open all input SMFs
        val readers = inputs.map(\path: SmfReader.open(path)?)?

        # 2. Create shared ObjTaker
        self.obj_taker = ObjTaker.create_multi(readers)

        # 3. Collect all deferred hints
        val all_hints = self.collect_deferred_hints(readers)

        # 4. Build link context
        val context = self.build_context(readers)

        # 5. Resolve deferred types across modules
        val resolved = self.resolve_cross_module(all_hints, context)?

        # 6. Take all required objects
        val objects = self.take_all_objects(readers, resolved)?

        # 7. Generate required specializations
        val specializations = self.generate_specializations(objects)?

        # 8. Write output
        match config.output_format:
            OutputFormat.Smf -> self.write_smf(output, objects, specializations)
            OutputFormat.Native -> self.link_with_mold(output, objects, specializations, config)

    fn collect_deferred_hints(readers: List<SmfReader>) -> List<DeferredHint>:
        readers.flat_map(\r: r.inference_hints.deferred_list())

    fn resolve_cross_module(hints: List<DeferredHint>, context: LinkContext) -> Result<Dict<DeferredTypeId, Type>, LinkError>:
        val engine = InferenceEngine.create()

        # Add all constraints from all modules
        for hint in hints:
            engine.add_deferred(hint)

        # Add cross-module unification constraints
        for unification in context.unifications:
            engine.unify_across(
                unification.from_module,
                unification.to_module,
                unification.type_var
            )?

        # Solve all constraints
        engine.solve()?

        # Return resolved mappings
        Ok(engine.get_resolutions())

    fn take_all_objects(readers: List<SmfReader>, resolved: Dict<DeferredTypeId, Type>) -> Result<List<ResolvedObject>, LinkError>:
        val objects = []

        for reader in readers:
            for symbol in reader.exported_symbols():
                val obj = self.obj_taker.take_object(symbol.name)?
                objects.push(obj)

        Ok(objects)

    fn generate_specializations(objects: List<ResolvedObject>) -> Result<List<Specialization>, LinkError>:
        # Find all generic usages that need instantiation
        val needed = objects.flat_map(\o: o.required_specializations())
            .unique()

        # Generate each specialization
        needed.map(\spec: self.obj_taker.instantiate_specialization(spec)?)

    fn link_with_mold(output: text, objects: List<ResolvedObject>, specs: List<Specialization>, config: LinkConfig) -> Result<(), LinkError>:
        val backend = MoldBackend.create(config)?

        # Write temporary object files
        val temp_dir = TempDir.create()?
        val obj_paths = objects.enumerate().map(\(i, obj):
            val path = "{temp_dir}/obj_{i}.o"
            self.write_elf_object(obj, path)?
            path
        )?

        # Add specializations
        for spec in specs:
            val path = "{temp_dir}/spec_{spec.name}.o"
            self.write_elf_object(spec.object, path)?
            obj_paths.push(path)

        # Execute mold
        backend.link(obj_paths, output, config)
```

### 5. Mold Backend (Simple + Rust FFI)

```simple
# simple/compiler/linker/mold.spl

extern class MoldFfi:
    # Rust FFI for mold execution
    static fn find_mold() -> Option<text>
    static fn execute(args: List<text>) -> Result<i32, text>

class MoldBackend:
    mold_path: text
    config: LinkConfig

    static fn create(config: LinkConfig) -> Result<MoldBackend, LinkError>:
        val path = MoldFfi.find_mold()
            .ok_or(LinkError.MoldNotFound)?

        Ok(MoldBackend(mold_path: path, config: config))

    fn link(obj_paths: List<text>, output: text, config: LinkConfig) -> Result<(), LinkError>:
        val args = ["-o", output]

        # Add object files
        for path in obj_paths:
            args.push(path)

        # Add libraries
        for lib in config.libraries:
            args.push("-l")
            args.push(lib)

        # PIE by default
        if config.pie:
            args.push("-pie")

        # Execute mold
        val result = MoldFfi.execute(args)?
        if result != 0:
            Err(LinkError.MoldFailed(result))
        else:
            Ok(())
```

---

## SMF Format Updates

### InferenceHints Section (Type 14)

**Binary Format** (Rust FFI handles):
```
InferenceHints Section (Type 14)
┌──────────────────────────────────────────────┐
│ Header (16 bytes)                            │
│   magic: "INFE" (4 bytes)                    │
│   version: u16                               │
│   hint_count: u32                            │
│   constraint_count: u32                      │
│   reserved: u16                              │
├──────────────────────────────────────────────┤
│ Hint Table (variable)                        │
├──────────────────────────────────────────────┤
│ Constraint Table (variable)                  │
└──────────────────────────────────────────────┘
```

### note.sdn Schema (Simple parses)

```sdn
# Type inference hints for link-time resolution
# Version: 2.0

type_vars |id, name, constraints, fallback|
    0, "T", "[Numeric]", "i64"
    1, "U", "[Iterable(T)]", "List<T>"

deferred |id, symbol, type_vars, usage_sites|
    0, "map_fn", "[T, U]", "app.spl:42,lib.spl:15"
    1, "identity", "[T]", "main.spl:10"

unifications |from_module, to_module, type_var, resolved_type|
    "lib", "app", "T", "Int"

link_specializations |id, template, type_args, generated_name|
    0, "List", "[Int]", "List$Int"

# END_INFERENCE
```

---

## Implementation Plan

### Phase 1: Type Inference Module in Simple (Week 1-2)

**Tasks**:
| ID | Task | File | Language |
|----|------|------|----------|
| 1.1 | Create inference module structure | `simple/compiler/inference/__init__.spl` | Simple |
| 1.2 | Implement Type enum | `simple/compiler/inference/types.spl` | Simple |
| 1.3 | Implement Unifier class | `simple/compiler/inference/unify.spl` | Simple |
| 1.4 | Implement InferenceEngine | `simple/compiler/inference/infer.spl` | Simple |
| 1.5 | Add constraint system | `simple/compiler/inference/constraints.spl` | Simple |
| 1.6 | Add deferred hints | `simple/compiler/inference/deferred.spl` | Simple |
| 1.7 | SDN serialization | `simple/compiler/inference/serialize.spl` | Simple |
| 1.8 | Write tests | `test/lib/std/unit/compiler/inference_spec.spl` | Simple |

### Phase 2: ObjTaker in Simple (Week 2-3)

**Tasks**:
| ID | Task | File | Language |
|----|------|------|----------|
| 2.1 | Create ObjTaker class | `simple/compiler/linker/obj_taker.spl` | Simple |
| 2.2 | Implement template loading | `simple/compiler/linker/obj_taker.spl` | Simple |
| 2.3 | Implement take_object methods | `simple/compiler/linker/obj_taker.spl` | Simple |
| 2.4 | Add template/instance caching | `simple/compiler/linker/obj_taker.spl` | Simple |
| 2.5 | Write tests | `test/lib/std/unit/compiler/obj_taker_spec.spl` | Simple |

### Phase 3: SMF Reader/Writer (Week 3-4)

**Tasks**:
| ID | Task | File | Language |
|----|------|------|----------|
| 3.1 | Create SmfReader Simple wrapper | `simple/compiler/linker/smf_reader.spl` | Simple |
| 3.2 | Create SmfWriter Simple wrapper | `simple/compiler/linker/smf_writer.spl` | Simple |
| 3.3 | Add InferenceHints section type | `src/rust/loader/src/smf/section.rs` | Rust |
| 3.4 | Implement Rust FFI for binary ops | `src/rust/loader/src/smf/ffi.rs` | Rust |
| 3.5 | SDN parsing for note.sdn | `simple/compiler/linker/note_sdn.spl` | Simple |
| 3.6 | Write tests | `test/lib/std/unit/compiler/smf_spec.spl` | Simple |

### Phase 4: Linker in Simple (Week 4-5)

**Tasks**:
| ID | Task | File | Language |
|----|------|------|----------|
| 4.1 | Create Linker class | `simple/compiler/linker/link.spl` | Simple |
| 4.2 | Implement link pipeline | `simple/compiler/linker/link.spl` | Simple |
| 4.3 | Cross-module type resolution | `simple/compiler/linker/link.spl` | Simple |
| 4.4 | MoldBackend wrapper | `simple/compiler/linker/mold.spl` | Simple |
| 4.5 | Mold FFI in Rust | `src/rust/compiler/src/linker/mold_ffi.rs` | Rust |
| 4.6 | Write tests | `test/lib/std/unit/compiler/linker_spec.spl` | Simple |

### Phase 5: Loader Integration (Week 5)

**Tasks**:
| ID | Task | File | Language |
|----|------|------|----------|
| 5.1 | Create Simple ModuleLoader | `simple/compiler/loader/module_loader.spl` | Simple |
| 5.2 | Integrate ObjTaker | `simple/compiler/loader/module_loader.spl` | Simple |
| 5.3 | Runtime instantiation | `simple/compiler/loader/instantiate.spl` | Simple |
| 5.4 | Write tests | `test/lib/std/unit/compiler/loader_spec.spl` | Simple |

### Phase 6: Testing and Documentation (Week 6)

**Tasks**:
| ID | Task | File | Language |
|----|------|------|----------|
| 6.1 | End-to-end integration tests | `test/system/features/inference/link_inference_spec.spl` | Simple |
| 6.2 | Performance benchmarks | `test/bench/inference_bench.spl` | Simple |
| 6.3 | Update SMF spec doc | `doc/format/smf_specification.md` | Markdown |
| 6.4 | Migration guide | `doc/guide/inference_migration.md` | Markdown |

---

## Rust FFI Minimal Surface

Only these Rust functions needed:

```rust
// src/rust/loader/src/smf/ffi.rs

#[no_mangle]
pub extern "C" fn smf_reader_open(path: *const c_char) -> *mut SmfReaderHandle;

#[no_mangle]
pub extern "C" fn smf_reader_read_header(handle: *mut SmfReaderHandle) -> SmfHeaderRaw;

#[no_mangle]
pub extern "C" fn smf_reader_read_section(handle: *mut SmfReaderHandle, index: u32) -> ByteBuffer;

#[no_mangle]
pub extern "C" fn smf_reader_read_symbols(handle: *mut SmfReaderHandle) -> SymbolTableRaw;

#[no_mangle]
pub extern "C" fn smf_reader_close(handle: *mut SmfReaderHandle);

// Mold execution
#[no_mangle]
pub extern "C" fn mold_find_path() -> *const c_char;

#[no_mangle]
pub extern "C" fn mold_execute(args: *const *const c_char, argc: usize) -> i32;
```

---

## Success Criteria

1. **Simple-First**: 80%+ code in Simple, only binary I/O in Rust
2. **Unified Inference**: Same inference for compiler, loader, linker
3. **Link-Time Instantiation**: Generics instantiated at link time
4. **No Regression**: Existing code works unchanged
5. **Performance**: Link-time inference adds <15% overhead

---

## File Summary

| Component | Simple Files | Rust Files |
|-----------|--------------|------------|
| Type Inference | 7 | 0 |
| ObjTaker | 1 | 0 |
| SMF Reader/Writer | 3 | 1 (FFI) |
| Linker | 2 | 1 (FFI) |
| Loader | 2 | 0 |
| Tests | 6 | 0 |
| **Total** | **21** | **2** |

---

## References

- SMF Format Spec: `doc/format/smf_specification.md`
- Type Inference Design: `doc/design/type_inference.md`
- Existing Rust SMF: `src/rust/loader/src/smf/`
- Mold Linker: https://github.com/rui314/mold
