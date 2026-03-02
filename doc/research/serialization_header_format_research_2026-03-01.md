# Serialization and Header Format Research

**Date:** 2026-03-01
**Status:** Complete
**Purpose:** Cross-language study of serialization systems and module interface formats
**Feeds into:** `doc/design/simple_header_binary_design.md`

---

## 1. Problem Analysis

Simple's watcher currently generates only SMF (compiled binary) on file change. There is no intermediate format that captures a module's **public interface** separate from its implementation. This forces dependents to re-parse full source even when only internal code changed.

Three related sub-problems:

1. **Header format** — What should a "parsed AST header" contain and how should it be structured?
2. **Serialization framework** — How should objects be serialized with customizable field inclusion?
3. **Type identification** — How should serialized types be identified across versions?

---

## 2. Languages Studied

### 2.1 Zig

**Serialization:** No built-in framework. Uses `comptime` (compile-time) reflection to generate serializers with zero runtime overhead. `@typeInfo(T)` introspects struct fields at compile time. Standard library has `std.json` using comptime reflection.

**Module interface:** No separate interface file. The `.zig` source file IS the interface — `pub` declarations are the API. Zig's incremental compilation uses **content-addressed cache** keyed by source hash + compiler flags. The compiler builds a module fingerprint from the AST, so dependents skip recompilation if the AST-visible interface is unchanged.

**Type identification:** Structural, via `comptime` shape inspection. No runtime type IDs.

**Field customization:** Done at `comptime` — filter `@typeInfo.Struct.fields` array by any comptime-evaluable condition. Fully general but requires the user to write the filter logic.

**Versioning:** Manual. Common pattern: tagged union with version field. No automatic schema evolution.

**Takeaway:** Comptime reflection is powerful but requires language-level support. Content-hash caching for incremental compilation is the standard approach.

### 2.2 Rust

**Serialization (.rmeta):** Rust generates `.rmeta` (Rust Metadata) binary files as module interfaces. These contain all `pub` types, function signatures, trait impls, generics templates, and inlineable MIR bodies. Encoded using `rustc_serialize` with lazy-loaded sections — items are only deserialized when accessed by downstream crates. A two-pass approach: items serialized to a buffer, then an index table maps `DefId` to byte offsets.

**Serialization (Serde):** The dominant user-space serialization framework. Uses derive macros to auto-generate `Serialize`/`Deserialize` impls. Key attributes:
- `#[serde(skip)]` — exclude field entirely
- `#[serde(skip_serializing_if = "Option::is_none")]` — conditional skip
- `#[serde(rename = "wire_name")]` — different wire vs code name
- `#[serde(default)]` — use Default::default() when missing on deserialize
- `#[serde(tag = "type", content = "data")]` — enum representation control
- `#[serde(flatten)]` — inline nested struct fields into parent
- `#[serde(with = "module")]` — custom serializer module

**Type identification:** `DefId` = crate hash + item index. Stable within a crate version but changes on crate hash change. Serde in JSON mode uses field names; Bincode uses positional order (fragile — reordering breaks compatibility).

**Incremental compilation:** `dep-graph.bin` stores a dependency graph alongside `.rmeta`. Each query result is fingerprinted with `SipHash`. If the fingerprint matches cached value, the query is skipped. Very granular — query-level, not file-level.

**Takeaway:** `.rmeta` is the gold standard for compiled module interfaces. Serde's attribute model is the most ergonomic field customization design. Lazy loading via offset tables is key for large modules.

### 2.3 Erlang/BEAM

**Serialization (ETF):** External Term Format is Erlang's universal binary format. Tag-byte-prefixed: `97` = small int, `100` = atom, `104` = tuple, `108` = list, `109` = binary, `116` = map. Self-describing — atom strings embedded in every term. Used for inter-process communication, `.beam` file literals, and `dets` persistence.

**BEAM file format:** Chunk-based binary (like IFF/RIFF): `"FOR1" <size:32> "BEAM" [chunks...]`. Each chunk: `<4-byte-name> <4-byte-size> <data> <padding>`. Key chunks:
- `AtU8` — atom table (all names deduplicated)
- `Code` — bytecode
- `ExpT` — export table (function + arity + label)
- `ImpT` — import table (module + function + arity)
- `LitT` — literal table (zlib-compressed ETF terms)

**Header files (.hrl):** Textual include files with record definitions, macros, and type specs. Re-parsed on every include — no compiled form. Module exports defined by `-export([fun/1])` attribute in `.erl` files.

**Type identification:** Atom string value. Renames break serialized data. No numeric IDs.

**Versioning:** Convention-based. Extend tuples: `{record_v2, field1, field2, new_field}`. Maps (key-value) are more resilient — adding a key doesn't break existing code.

**Takeaway:** Chunk-based format is robust and extensible. Atom table (string interning) is essential for binary efficiency. Self-describing format trades size for debuggability.

### 2.4 Java

**Serialization (.class):** Binary constant pool with indexed entries. Class identified by fully qualified name (`java/lang/String`). Fields and methods reference constant pool entries by index. The `Signature` attribute preserves generic type info (erased at runtime). Structure: magic `0xCAFEBABE`, version, constant pool, access flags, class/super/interfaces, fields, methods, attributes.

**Java Serialization (Serializable):** Binary format with class name + `serialVersionUID` (long). The UID is a SHA-1 hash of the class structure if not declared explicitly. Mismatch → `InvalidClassException`. `transient` keyword excludes fields. `Externalizable` gives full manual control. `readObject`/`writeObject` hooks for custom logic. Adding fields with declared UID works if field has default; missing fields become zero/null.

**Protocol Buffers:** Field-tag-based binary format. Each field encoded as `(tag << 3) | wire_type`. Tags are integers, not names — renaming is free, reordering is free, only tag number change breaks compatibility. `optional` fields with `reserved` tag numbers for deleted fields.

**Takeaway:** `serialVersionUID` (class structure hash) automatically catches incompatible changes. Protobuf's integer tag approach is the most robust for evolution. Constant pool (string interning) is proven at massive scale.

### 2.5 Ruby

**Serialization (Marshal):** Binary format with type-byte prefix. Objects identified by class name symbol. Custom hooks: `marshal_dump` returns array of data to persist; `marshal_load` reconstructs from array. Type `'U'` tag in stream invokes these hooks. Back-references with `'@'` tag for shared object identity.

**Interface files (.rbi — Sorbet):** Text stubs with `sig` blocks for type checking. Pure Ruby syntax with empty method bodies. Generated by `tapioca` for gems. Processed only by Sorbet type checker, not Ruby runtime.

**Type identification:** Class name as Symbol string. `const_get` lookup during load.

**Field customization:** Only via `marshal_dump`/`marshal_load` — no annotations, no attributes. Filter `instance_variables` manually.

**Versioning:** Position-based in `marshal_dump` array. Check array length in `marshal_load` and provide defaults for missing positions.

**Takeaway:** Custom serialization hooks (marshal_dump/load) pattern is simple but manual. Text stub files (.rbi) for type interfaces are practical for dynamically typed languages.

### 2.6 TypeScript

**Serialization:** No built-in binary serialization. JSON is the standard interchange format.

**Declaration files (.d.ts):** Text files containing only type information — no runtime code. Auto-generated by `tsc --declaration` or written manually for JS libraries. Contain `declare` keyword for runtime-existing items. Support `export type` (type-only exports, erased at compile time) and `import type` (type-only imports).

**The .js + .d.ts pattern:** Distributed as compiled JS (runtime) + .d.ts (compile-time interface). `package.json` maps `"types"` to the `.d.ts` path.

**Type identification:** Structural for interfaces/type aliases (duck typing — same shape = compatible). Nominal for classes/enums (runtime identity matters).

**Incremental compilation:** `.tsbuildinfo` file (JSON) stores file graph with content hashes and output fingerprints. Project references allow `.d.ts` generation per subproject — dependents only parse the `.d.ts`.

**Takeaway:** Auto-generated `.d.ts` from source is the exact pattern we want for `.shb`. Content-hash `.tsbuildinfo` for incremental builds. Structural typing means interface changes are purely about shape, not names.

---

## 3. Comparative Analysis

### 3.1 Binary vs Text Interface Formats

| Format | Type | Self-Describing? | Speed | Debuggable |
|--------|------|-----------------|-------|------------|
| Rust `.rmeta` | Binary | No | Fast | No |
| Erlang `.beam` | Binary | Partially | Fast | Hex dump |
| Java `.class` | Binary | Partially | Fast | javap tool |
| TypeScript `.d.ts` | Text | Yes | Moderate | Yes |
| Ruby `.rbi` | Text | Yes | Moderate | Yes |
| Zig (none) | N/A | N/A | Source re-parse | Yes |

**Conclusion:** Binary for production speed, text companion for debugging. Both generated from same extraction.

### 3.2 Type Identification Strategies

| Strategy | Used By | Rename Safe? | Reorder Safe? | Structural Check? |
|----------|---------|-------------|--------------|-------------------|
| Name string | Erlang ETF, Ruby Marshal | No | Yes | No |
| FQ class name | Java .class | No | Yes | No |
| DefId (hash+idx) | Rust .rmeta | No | Yes | No |
| Structural shape | Zig comptime, TS interfaces | Yes | Yes | Inherent |
| Integer tag | Protobuf | Yes | Yes | No |
| Name + struct hash | Java Serializable | No | Partial | Yes (UID) |

**Conclusion:** No single strategy covers all needs. A **triple identification** (positional, stable tag, structural hash) covers all use cases.

### 3.3 Field Customization Approaches

| Approach | Language | Granularity | Ergonomics |
|----------|----------|-------------|------------|
| Annotation/attribute | Rust Serde, Java | Per-field | Excellent |
| Keyword | Java (`transient`) | Per-field | Good (limited) |
| Comptime filter | Zig | Arbitrary | Powerful but manual |
| Custom hooks | Ruby (`marshal_dump`) | Whole object | Flexible but verbose |
| None built-in | Erlang, TypeScript | N/A | Manual |

**Conclusion:** Annotation-based (like Serde) is the best balance of power and ergonomics.

### 3.4 Versioning Mechanisms

| Mechanism | Language | Automatic? | Backward Compat? |
|-----------|----------|-----------|-----------------|
| Content hash | Zig, TS `.tsbuildinfo` | Yes | Binary: yes/no |
| Fingerprint | Rust dep-graph | Yes | Granular queries |
| Structure hash | Java `serialVersionUID` | Yes (if auto) | Strict mismatch |
| Integer tags | Protobuf | Manual assign | Strong (reserved) |
| Convention | Erlang, Ruby | No | Fragile |

**Conclusion:** Auto-computed content/structure hash for detection + manual stable tags for evolution = best of both worlds.

---

## 4. Recommendations for Simple

### 4.1 Header Format → `.shb` (Simple Header Binary)

Adopt the **Rust `.rmeta` + TypeScript `.d.ts` pattern**: auto-generated binary interface file, generated alongside SMF during compilation/watch.

- **64-byte header** (half of SMF — interface is simpler than compiled module)
- **Section-based** (like SMF/BEAM chunks) for extensibility
- **String table** (like ELF `.strtab`) for name deduplication
- **SDN companion** (`.shd`) for debugging/diffing

### 4.2 Serialization → Triple ID System

Combine the best of Protobuf, Java, and Rust:

| ID | Inspiration | Purpose |
|----|------------|---------|
| `obj_id` (positional) | Protobuf wire format | Fast binary lookup |
| `serial_id` (stable tag) | Protobuf field numbers | Cross-version stability |
| `class_hash` (structural) | Java `serialVersionUID` | Incompatibility detection |

### 4.3 Field Customization → Serde-style Annotations

```simple
@serial_id(1)
@skip
@skip_if_nil
@default(value)
@rename("wire_name")
@flatten
@transient
```

### 4.4 Watcher Enhancement → Two-Level Hash Check

```
Level 1: source_hash   → Recompile the file itself (always)
Level 2: interface_hash → Recompile dependents (only if interface changed)
```

This is the key optimization: internal-only changes never cascade.

### 4.5 Existing Infrastructure to Reuse

| Component | Location | Reuse For |
|-----------|----------|-----------|
| `ApiSurface` class | `src/compiler/90.tools/api_surface.spl` | Header AST data model |
| `SmfHeader` patterns | `src/compiler/70.backend/linker/smf_header.spl` | Binary format conventions |
| `IncrementalState` | `src/compiler/80.driver/incremental.spl` | Hash tracking, dependency graph |
| Visibility model | `src/compiler/00.common/visibility.spl` | Public/private filtering |
| HIR serialize | `src/compiler/20.hir/inference/serialize.spl` | SDN serialization patterns |
| Mono metadata | `src/compiler/40.mono/monomorphize/metadata.spl` | Generic template tracking |
| SDN handler traits | `doc/design/sdn_handler_trait_design.md` | SDN parsing architecture |
| Watch orchestrator | `src/compiler/80.driver/build/watch.spl` | Watcher integration point |

---

## 5. Open Questions

1. **Generic bodies in headers?** — Generics that need monomorphization may require the template body, not just the signature. Should `.shb` include a `GENERIC_BODIES` section with MIR for inlineable generics (like Rust `.rmeta`)?

2. **Trait impl tracking?** — Should `.shb` list all `impl Trait for Type` in the module? Downstream modules need this for trait resolution. Rust `.rmeta` includes all impls.

3. **Macro/mixin bodies?** — `mixin(code_text)` requires the actual code string. Should `.shb` include mixin source text for downstream expansion?

4. **SDN or custom binary for `.shd`?** — SDN is human-readable but may need extensions for representing complex type signatures. Could use SDN tables for flat data.

5. **Serial ID persistence format?** — Auto-assigned serial IDs need persistent storage. Options: `.sdn` file, embedded in source comments, or dedicated `.serial_ids` file.

---

## 6. References

- [Rust .rmeta format](https://rustc-dev-guide.rust-lang.org/backend/libs-and-metadata.html)
- [Protobuf encoding](https://protobuf.dev/programming-guides/encoding/)
- [BEAM file format](https://www.erlang.org/doc/apps/erts/beam_file_format)
- [TypeScript declaration files](https://www.typescriptlang.org/docs/handbook/declaration-files/introduction.html)
- [Serde attributes](https://serde.rs/attributes.html)
- [Java serialization spec](https://docs.oracle.com/en/java/javase/21/docs/specs/serialization/)
- [Zig comptime](https://ziglang.org/documentation/master/#comptime)
- [Ruby Marshal format](https://ruby-doc.org/3.3/Marshal.html)
