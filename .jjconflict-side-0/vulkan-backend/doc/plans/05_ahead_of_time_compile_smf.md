# AOT Compilation: SMF Linker and Pipeline

Part of [Ahead of Time Compilation Plan](05_ahead_of_time_compile.md).

## SMF Linker

### SMF Emission (linker/emit.rs)

```rust
// crates/compiler/src/linker/emit.rs

use std::io::Write;
use crate::smf::*;

pub struct SmfEmitter {
    header: SmfHeader,
    sections: Vec<(SmfSection, Vec<u8>)>,
    symbols: Vec<SmfSymbol>,
    string_table: Vec<u8>,
    relocations: Vec<SmfRelocation>,
}

impl SmfEmitter {
    pub fn new() -> Self {
        Self {
            header: SmfHeader::default(),
            sections: Vec::new(),
            symbols: Vec::new(),
            string_table: vec![0],  // Start with null byte
            relocations: Vec::new(),
        }
    }

    pub fn set_executable(&mut self, entry_offset: u64) {
        self.header.flags |= SMF_FLAG_EXECUTABLE;
        self.header.entry_point = entry_offset;
    }

    pub fn set_reloadable(&mut self) {
        self.header.flags |= SMF_FLAG_RELOADABLE;
    }

    pub fn add_code(&mut self, code: Vec<u8>) {
        let section = SmfSection {
            section_type: SectionType::Code,
            flags: SECTION_FLAG_READ | SECTION_FLAG_EXEC,
            offset: 0,  // Filled in during emit
            size: code.len() as u64,
            virtual_size: code.len() as u64,
            alignment: 16,
            name: *b".text\0\0\0\0\0\0\0\0\0\0\0",
        };
        self.sections.push((section, code));
    }

    pub fn add_data(&mut self, data: Vec<u8>, readonly: bool) {
        let section = SmfSection {
            section_type: if readonly { SectionType::RoData } else { SectionType::Data },
            flags: SECTION_FLAG_READ | if readonly { 0 } else { SECTION_FLAG_WRITE },
            offset: 0,
            size: data.len() as u64,
            virtual_size: data.len() as u64,
            alignment: 8,
            name: if readonly {
                *b".rodata\0\0\0\0\0\0\0\0\0"
            } else {
                *b".data\0\0\0\0\0\0\0\0\0\0\0"
            },
        };
        self.sections.push((section, data));
    }

    pub fn add_symbol(&mut self, name: &str, sym_type: SymbolType, binding: SymbolBinding, value: u64, size: u64) {
        let name_offset = self.string_table.len() as u32;
        self.string_table.extend_from_slice(name.as_bytes());
        self.string_table.push(0);

        self.symbols.push(SmfSymbol {
            name_offset,
            name_hash: hash_name(name),
            sym_type,
            binding,
            visibility: 0,
            flags: 0,
            value,
            size,
            type_id: 0,
            version: 1,
        });
    }

    pub fn add_relocation(&mut self, offset: u64, symbol_index: u32, reloc_type: RelocationType, addend: i64) {
        self.relocations.push(SmfRelocation {
            offset,
            symbol_index,
            reloc_type,
            addend,
        });
    }

    pub fn emit<W: Write>(&mut self, writer: &mut W) -> std::io::Result<()> {
        // Calculate offsets
        let mut offset = SmfHeader::SIZE as u64;

        // Section table offset
        self.header.section_table_offset = offset;
        self.header.section_count = self.sections.len() as u32;
        offset += (self.sections.len() * std::mem::size_of::<SmfSection>()) as u64;

        // Update section offsets
        for (section, data) in &mut self.sections {
            // Align
            let alignment = section.alignment as u64;
            offset = (offset + alignment - 1) & !(alignment - 1);
            section.offset = offset;
            offset += data.len() as u64;
        }

        // Relocation section
        if !self.relocations.is_empty() {
            let reloc_size = (self.relocations.len() * std::mem::size_of::<SmfRelocation>()) as u64;
            let reloc_section = SmfSection {
                section_type: SectionType::Reloc,
                flags: SECTION_FLAG_READ,
                offset,
                size: reloc_size,
                virtual_size: reloc_size,
                alignment: 8,
                name: *b".reloc\0\0\0\0\0\0\0\0\0\0",
            };
            offset += reloc_size;
            // Add relocation section (data will be written separately)
        }

        // Symbol table
        self.header.symbol_table_offset = offset;
        self.header.symbol_count = self.symbols.len() as u32;
        offset += (self.symbols.len() * std::mem::size_of::<SmfSymbol>()) as u64;

        // String table follows symbols
        offset += self.string_table.len() as u64;

        // Write header
        self.header.magic = *SMF_MAGIC;
        self.header.version_major = 1;
        self.header.version_minor = 0;

        #[cfg(target_os = "linux")]
        { self.header.platform = Platform::Linux as u8; }
        #[cfg(target_os = "windows")]
        { self.header.platform = Platform::Windows as u8; }

        #[cfg(target_arch = "x86_64")]
        { self.header.arch = Arch::X86_64 as u8; }

        writer.write_all(as_bytes(&self.header))?;

        // Write section table
        for (section, _) in &self.sections {
            writer.write_all(as_bytes(section))?;
        }

        // Write section data
        for (section, data) in &self.sections {
            // Padding for alignment
            let current_pos = SmfHeader::SIZE
                + self.sections.len() * std::mem::size_of::<SmfSection>();
            let target_pos = section.offset as usize;
            let padding = target_pos.saturating_sub(current_pos);
            writer.write_all(&vec![0u8; padding])?;

            writer.write_all(data)?;
        }

        // Write relocations
        for reloc in &self.relocations {
            writer.write_all(as_bytes(reloc))?;
        }

        // Write symbols
        for sym in &self.symbols {
            writer.write_all(as_bytes(sym))?;
        }

        // Write string table
        writer.write_all(&self.string_table)?;

        Ok(())
    }
}

fn as_bytes<T>(value: &T) -> &[u8] {
    unsafe {
        std::slice::from_raw_parts(
            value as *const T as *const u8,
            std::mem::size_of::<T>(),
        )
    }
}
```

---

## Compilation Pipeline

```rust
// crates/compiler/src/pipeline.rs

use std::path::Path;
use std::fs::File;
use std::io::BufWriter;

use crate::parser::SimpleParser;
use crate::hir::HirLowering;
use crate::mir::MirLowering;
use crate::codegen::CraneliftCodegen;
use crate::linker::SmfEmitter;
use crate::cache::CompilationCache;

pub struct CompilerPipeline {
    parser: SimpleParser,
    cache: CompilationCache,
}

impl CompilerPipeline {
    pub fn new() -> Result<Self, String> {
        Ok(Self {
            parser: SimpleParser::new()?,
            cache: CompilationCache::new(),
        })
    }

    /// Compile source file to SMF
    pub fn compile(&mut self, source_path: &Path, output_path: &Path) -> Result<(), CompileError> {
        // Check cache
        let source_hash = self.cache.hash_file(source_path)?;
        if let Some(cached) = self.cache.get(source_path, source_hash) {
            std::fs::copy(&cached, output_path)?;
            return Ok(());
        }

        // Read source
        let source = std::fs::read_to_string(source_path)?;

        // Parse
        let ast = self.parser.parse(&source)?;

        // Lower to HIR
        let mut hir_lower = HirLowering::new();
        let hir = hir_lower.lower_module(&ast)?;

        // Lower to MIR
        let mut mir_lower = MirLowering::new();
        let mir = mir_lower.lower_module(&hir)?;

        // Generate code
        let mut codegen = CraneliftCodegen::new("x86_64")?;
        let object_code = codegen.compile_module(&mir)?;

        // Emit SMF
        let mut emitter = SmfEmitter::new();
        emitter.add_code(object_code);

        // Add symbols
        for func in &mir.functions {
            emitter.add_symbol(
                &func.name,
                SymbolType::Function,
                if func.is_public { SymbolBinding::Global } else { SymbolBinding::Local },
                0,  // TODO: Calculate offset
                0,
            );
        }

        // Check for main function
        if mir.functions.iter().any(|f| f.name == "main") {
            emitter.set_executable(0);  // TODO: Calculate main offset
        }

        // Write output
        let file = File::create(output_path)?;
        let mut writer = BufWriter::new(file);
        emitter.emit(&mut writer)?;

        // Update cache
        self.cache.store(source_path, source_hash, output_path)?;

        Ok(())
    }

    /// Compile and run (interpreter-like workflow)
    pub fn compile_and_run(&mut self, source_path: &Path) -> Result<i32, CompileError> {
        // Determine output path
        let output_path = source_path.with_extension("smf");

        // Compile if needed
        if self.needs_recompile(source_path, &output_path)? {
            self.compile(source_path, &output_path)?;
        }

        // Load and run
        let loader = crate::loader::ModuleLoader::new();
        let module = loader.load(&output_path)?;

        // Get entry point
        type MainFn = extern "C" fn() -> i32;
        let main: MainFn = module.entry_point()
            .ok_or(CompileError::NoEntryPoint)?;

        Ok(main())
    }

    fn needs_recompile(&self, source: &Path, output: &Path) -> Result<bool, CompileError> {
        if !output.exists() {
            return Ok(true);
        }

        let source_modified = source.metadata()?.modified()?;
        let output_modified = output.metadata()?.modified()?;

        Ok(source_modified > output_modified)
    }
}

#[derive(Debug)]
pub enum CompileError {
    Io(std::io::Error),
    Parse(String),
    Lower(String),
    Codegen(String),
    Link(String),
    NoEntryPoint,
}
```

---

## Cargo.toml

```toml
[package]
name = "simple-compiler"
version = "0.1.0"
edition = "2021"

[dependencies]
cranelift = "0.107"
cranelift-codegen = "0.107"
cranelift-module = "0.107"
cranelift-object = "0.107"
cranelift-native = "0.107"
target-lexicon = "0.12"

simple-parser = { path = "../parser" }
simple-loader = { path = "../loader" }
```

---

## Summary

| Stage | Input | Output | Purpose |
|-------|-------|--------|---------|
| Parser | Source (.simple) | AST | Syntax analysis |
| HIR Lowering | AST | HIR | Type checking, desugaring |
| MIR Lowering | HIR | MIR | Control flow, basic blocks |
| Codegen | MIR | Object code | Native code generation |
| Linker | Object code | SMF | Package into loadable module |

This pipeline enables the interpreter-like workflow: source changes trigger automatic recompilation before execution.
---

Back to: [Ahead of Time Compilation Plan](05_ahead_of_time_compile.md)
