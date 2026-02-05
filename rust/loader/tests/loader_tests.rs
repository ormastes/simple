use std::io::Cursor;
use std::sync::Arc;

use simple_loader::loader::ModuleLoader;
use simple_loader::registry::ModuleRegistry;
use simple_loader::smf::{
    apply_relocations, hash_name, Arch, Platform, RelocationType, SectionType, SmfHeader, SmfRelocation, SmfSection,
    SmfSymbol, SymbolBinding, SymbolTable, SymbolType, SECTION_FLAG_EXEC, SECTION_FLAG_READ, SECTION_FLAG_WRITE,
    SMF_FLAG_EXECUTABLE, SMF_FLAG_RELOADABLE, SMF_MAGIC,
};

fn push_struct<T: Copy>(buf: &mut Vec<u8>, value: &T) {
    let slice = unsafe { std::slice::from_raw_parts(value as *const T as *const u8, std::mem::size_of::<T>()) };
    buf.extend_from_slice(slice);
}

/// Helper to build SMF test modules with less boilerplate
struct SmfBuilder {
    filename: String,
    symbol_name: String,
    code_bytes: Vec<u8>,
    relocations: Vec<SmfRelocation>,
    exported_count: u32,
    flags: u32,
    sym_type: SymbolType,
    sym_binding: SymbolBinding,
    source_hash: u64,
}

impl SmfBuilder {
    fn new(filename: &str, symbol_name: &str) -> Self {
        Self {
            filename: filename.to_string(),
            symbol_name: symbol_name.to_string(),
            code_bytes: vec![0xC3u8], // ret
            relocations: Vec::new(),
            exported_count: 1,
            flags: SMF_FLAG_EXECUTABLE,
            sym_type: SymbolType::Function,
            sym_binding: SymbolBinding::Global,
            source_hash: 0,
        }
    }

    fn with_code(mut self, code: Vec<u8>) -> Self {
        self.code_bytes = code;
        self
    }

    fn with_relocation(mut self, reloc: SmfRelocation) -> Self {
        self.relocations.push(reloc);
        self
    }

    fn with_exported_count(mut self, count: u32) -> Self {
        self.exported_count = count;
        self
    }

    fn with_flags(mut self, flags: u32) -> Self {
        self.flags = flags;
        self
    }

    fn with_sym_type(mut self, sym_type: SymbolType) -> Self {
        self.sym_type = sym_type;
        self
    }

    fn with_sym_binding(mut self, binding: SymbolBinding) -> Self {
        self.sym_binding = binding;
        self
    }

    fn with_source_hash(mut self, hash: u64) -> Self {
        self.source_hash = hash;
        self
    }

    fn reloadable(self) -> Self {
        self.with_flags(SMF_FLAG_EXECUTABLE | SMF_FLAG_RELOADABLE)
    }

    fn library(self) -> Self {
        self.with_flags(0)
    }

    fn data_symbol(self) -> Self {
        self.with_sym_type(SymbolType::Data)
    }

    fn local_symbol(self) -> Self {
        self.with_sym_binding(SymbolBinding::Local).with_exported_count(0)
    }

    fn build(self) -> (tempfile::TempDir, std::path::PathBuf) {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join(&self.filename);

        let section_count = if self.relocations.is_empty() { 1 } else { 2 };
        let section_table_offset = SmfHeader::SIZE as u64;
        let section_table_size = std::mem::size_of::<SmfSection>() as u64 * section_count as u64;
        let code_offset = section_table_offset + section_table_size;

        let reloc_offset = code_offset + self.code_bytes.len() as u64;
        let reloc_size = std::mem::size_of::<SmfRelocation>() as u64 * self.relocations.len() as u64;
        let symbol_table_offset = reloc_offset + reloc_size;

        let header = SmfHeader {
            magic: *SMF_MAGIC,
            version_major: 0,
            version_minor: 1,
            platform: Platform::Any as u8,
            arch: Arch::X86_64 as u8,
            flags: self.flags,
            section_count,
            section_table_offset,
            symbol_table_offset,
            symbol_count: 1,
            exported_count: self.exported_count,
            entry_point: 0,
            module_hash: 0,
            source_hash: self.source_hash,
            app_type: 0,
            window_width: 0,
            window_height: 0,
            prefetch_hint: 0,
            prefetch_file_count: 0,
            reserved: [0; 5],
            compression: 0,
            compression_level: 0,
            reserved_compression: [0; 2],
            stub_size: 0,
            smf_data_offset: 0,
        };

        let code_section = Self::make_section(
            b"code",
            SectionType::Code,
            SECTION_FLAG_READ | SECTION_FLAG_EXEC,
            code_offset,
            self.code_bytes.len() as u64,
            16,
        );

        let string_table = format!("{}\0", self.symbol_name).into_bytes();
        let symbol = SmfSymbol {
            name_offset: 0,
            name_hash: hash_name(&self.symbol_name),
            sym_type: self.sym_type,
            binding: self.sym_binding,
            visibility: 0,
            flags: 0,
            value: 0,
            size: 0,
            type_id: 0,
            version: 0,
            template_param_count: 0,
            reserved: [0; 3],
            template_offset: 0,
        };

        let mut buf = Vec::new();
        push_struct(&mut buf, &header);
        push_struct(&mut buf, &code_section);

        if !self.relocations.is_empty() {
            let reloc_section = Self::make_section(
                b"reloc",
                SectionType::Reloc,
                SECTION_FLAG_READ,
                reloc_offset,
                reloc_size,
                8,
            );
            push_struct(&mut buf, &reloc_section);
        }

        buf.extend_from_slice(&self.code_bytes);
        for reloc in &self.relocations {
            push_struct(&mut buf, reloc);
        }
        push_struct(&mut buf, &symbol);
        buf.extend_from_slice(&string_table);

        std::fs::write(&path, &buf).unwrap();
        (dir, path)
    }

    fn make_section(
        name: &[u8],
        section_type: SectionType,
        flags: u32,
        offset: u64,
        size: u64,
        alignment: u64,
    ) -> SmfSection {
        let mut sec_name = [0u8; 16];
        let len = name.len().min(16);
        sec_name[..len].copy_from_slice(&name[..len]);
        SmfSection {
            section_type,
            flags,
            offset,
            size,
            virtual_size: size,
            alignment,
            name: sec_name,
        }
    }
}

fn make_minimal_module() -> (tempfile::TempDir, std::path::PathBuf) {
    SmfBuilder::new("module.smf", "entry").build()
}

#[test]
fn smf_header_rejects_bad_magic() {
    let mut bad = vec![0u8; SmfHeader::SIZE];
    bad[..4].copy_from_slice(b"BAD!");

    let mut cursor = Cursor::new(bad);
    let err = SmfHeader::read(&mut cursor).unwrap_err();
    assert_eq!(err.kind(), std::io::ErrorKind::InvalidData);
}

#[test]
fn symbol_table_resolves_by_name() {
    let name_bytes = b"foo\0bar\0".to_vec();
    let sym_foo = SmfSymbol {
        name_offset: 0,
        name_hash: hash_name("foo"),
        sym_type: SymbolType::Function,
        binding: SymbolBinding::Local,
        visibility: 0,
        flags: 0,
        value: 123,
        size: 0,
        type_id: 0,
        version: 0,
        template_param_count: 0,
        reserved: [0; 3],
        template_offset: 0,
    };
    let sym_bar = SmfSymbol {
        name_offset: 4,
        name_hash: hash_name("bar"),
        sym_type: SymbolType::Data,
        binding: SymbolBinding::Global,
        visibility: 0,
        flags: 0,
        value: 456,
        size: 0,
        type_id: 0,
        version: 0,
        template_param_count: 0,
        reserved: [0; 3],
        template_offset: 0,
    };

    let table = SymbolTable::new(vec![sym_foo, sym_bar], name_bytes.clone());

    let foo = table.lookup("foo").unwrap();
    assert_eq!(foo.value, 123);
    let bar_name = table.symbol_name(table.lookup("bar").unwrap());
    assert_eq!(bar_name, "bar");
}

#[test]
fn relocations_patch_local_symbol() {
    let sym = SmfSymbol {
        name_offset: 0,
        name_hash: hash_name("local"),
        sym_type: SymbolType::Data,
        binding: SymbolBinding::Local,
        visibility: 0,
        flags: 0,
        value: 0x30,
        size: 0,
        type_id: 0,
        version: 0,
        template_param_count: 0,
        reserved: [0; 3],
        template_offset: 0,
    };
    let string_table = b"local\0".to_vec();
    let table = SymbolTable::new(vec![sym], string_table);

    let mut code = vec![0u8; 16];
    let relocs = vec![SmfRelocation {
        offset: 0,
        symbol_index: 0,
        reloc_type: RelocationType::Abs64,
        addend: 0,
    }];

    let base = code.as_ptr() as usize;
    apply_relocations(
        &mut code,
        &relocs,
        &table,
        base,
        &|_| Some(0usize), // unused for local
    )
    .unwrap();

    let patched = u64::from_le_bytes(code[..8].try_into().unwrap());
    assert_eq!(patched, (base + 0x30) as u64);
}

fn make_exporting_module(name: &str) -> (tempfile::TempDir, std::path::PathBuf) {
    SmfBuilder::new(&format!("{name}.smf"), name).build()
}

fn make_importing_module(import_name: &str) -> (tempfile::TempDir, std::path::PathBuf) {
    SmfBuilder::new("importer.smf", import_name)
        .with_code(vec![0u8; 8])
        .with_relocation(SmfRelocation {
            offset: 0,
            symbol_index: 0,
            reloc_type: RelocationType::Abs64,
            addend: 0,
        })
        .with_exported_count(0)
        .build()
}

#[test]
fn loader_reads_minimal_module() {
    let (_dir, path) = make_minimal_module();
    let loader = ModuleLoader::new();
    let module = loader.load(&path).expect("module should load");

    assert!(module.header.is_executable());
    let entry: Option<unsafe extern "C" fn()> = module.entry_point();
    assert!(entry.is_some());

    let bytes = unsafe { std::slice::from_raw_parts(module.code_mem.as_ptr(), 1) };
    assert_eq!(bytes[0], 0xC3);
}

#[test]
fn registry_caches_module() {
    let (_dir, path) = make_minimal_module();
    let registry = ModuleRegistry::new();

    let first = registry.load(&path).unwrap();
    let second = registry.load(&path).unwrap();
    assert!(Arc::ptr_eq(&first, &second));

    let addr = registry.resolve_symbol("entry");
    assert!(addr.is_some());
}

#[test]
fn loader_resolves_imports_via_registry() {
    let (_prov_dir, provider_path) = make_exporting_module("ext");
    let (_imp_dir, importer_path) = make_importing_module("ext");

    let registry = ModuleRegistry::new();
    let provider = registry.load(&provider_path).expect("provider loads");

    let importer = registry.load(&importer_path).expect("importer loads");

    // First 8 bytes of importer code should be patched to provider entry address.
    let patched = {
        let bytes = unsafe { std::slice::from_raw_parts(importer.code_mem.as_ptr(), 8) };
        usize::from_le_bytes(bytes.try_into().unwrap())
    };
    let expected = provider.code_mem.as_ptr() as usize + 0;
    assert_eq!(patched, expected);
}

// ============== SmfSection Tests ==============

#[test]
fn section_name_str_returns_trimmed_name() {
    let section = SmfBuilder::make_section(b"code", SectionType::Code, 0, 0, 0, 16);
    assert_eq!(section.name_str(), "code");

    // Test longer name
    let section2 = SmfBuilder::make_section(b"longer_name", SectionType::Data, 0, 0, 0, 16);
    assert_eq!(section2.name_str(), "longer_name");

    // Test max length name (16 bytes, no null terminator)
    let section3 = SmfBuilder::make_section(b"0123456789abcdef", SectionType::RoData, 0, 0, 0, 16);
    assert_eq!(section3.name_str(), "0123456789abcdef");
}

#[test]
fn section_flags_correctly_identify_permissions() {
    // Executable section
    let exec_section = SmfBuilder::make_section(
        b"code",
        SectionType::Code,
        SECTION_FLAG_READ | SECTION_FLAG_EXEC,
        0,
        0,
        16,
    );
    assert!(exec_section.is_executable());
    assert!(!exec_section.is_writable());

    // Writable section
    let data_section = SmfBuilder::make_section(
        b"data",
        SectionType::Data,
        SECTION_FLAG_READ | SECTION_FLAG_WRITE,
        0,
        0,
        16,
    );
    assert!(!data_section.is_executable());
    assert!(data_section.is_writable());

    // Read-only section
    let ro_section = SmfBuilder::make_section(b"rodata", SectionType::RoData, SECTION_FLAG_READ, 0, 0, 16);
    assert!(!ro_section.is_executable());
    assert!(!ro_section.is_writable());

    // All flags
    let all_section = SmfBuilder::make_section(
        b"all",
        SectionType::Code,
        SECTION_FLAG_READ | SECTION_FLAG_WRITE | SECTION_FLAG_EXEC,
        0,
        0,
        16,
    );
    assert!(all_section.is_executable());
    assert!(all_section.is_writable());
}

// ============== Module Method Tests ==============

#[test]
fn module_get_function_returns_none_for_data_symbol() {
    let (_dir, path) = SmfBuilder::new("data.smf", "data_sym")
        .data_symbol()
        .with_source_hash(12345)
        .build();

    let loader = ModuleLoader::new();
    let module = loader.load(&path).expect("should load");

    // get_function should return None for data symbol
    let func: Option<unsafe extern "C" fn()> = module.get_function("data_sym");
    assert!(func.is_none(), "get_function should return None for data symbol");

    // source_hash should be readable
    assert_eq!(module.source_hash(), 12345);
}

#[test]
fn module_entry_point_returns_none_for_non_executable() {
    let (_dir, path) = SmfBuilder::new("lib.smf", "func").library().build();

    let loader = ModuleLoader::new();
    let module = loader.load(&path).expect("should load");

    // entry_point should return None for non-executable
    let entry: Option<unsafe extern "C" fn()> = module.entry_point();
    assert!(
        entry.is_none(),
        "entry_point should return None for non-executable module"
    );

    // But get_function should still work
    let func: Option<unsafe extern "C" fn()> = module.get_function("func");
    assert!(func.is_some(), "get_function should work on library module");
}

#[test]
fn module_exports_lists_global_symbols() {
    let (_dir, path) = make_minimal_module();
    let loader = ModuleLoader::new();
    let module = loader.load(&path).expect("should load");

    let exports = module.exports();
    assert!(!exports.is_empty());
    assert!(exports
        .iter()
        .any(|(name, ty)| *name == "entry" && *ty == SymbolType::Function));
}

#[test]
fn module_is_reloadable_checks_flag() {
    // Non-reloadable module (default)
    let (_dir1, path1) = make_minimal_module();
    let loader = ModuleLoader::new();
    let module1 = loader.load(&path1).expect("should load");
    assert!(!module1.is_reloadable());

    // Reloadable module
    let (_dir2, path2) = SmfBuilder::new("reloadable.smf", "entry").reloadable().build();

    let module2 = loader.load(&path2).expect("should load");
    assert!(module2.is_reloadable());
}

// ============== DynModule Trait Tests ==============

#[test]
fn dyn_module_trait_get_fn_works() {
    use simple_common::DynModule;

    let (_dir, path) = make_minimal_module();
    let loader = ModuleLoader::new();
    let module = loader.load(&path).expect("should load");

    // Use trait method
    let func: Option<unsafe extern "C" fn()> = DynModule::get_fn(&module, "entry");
    assert!(func.is_some());

    let missing: Option<unsafe extern "C" fn()> = DynModule::get_fn(&module, "nonexistent");
    assert!(missing.is_none());
}

#[test]
fn dyn_module_trait_entry_fn_works() {
    use simple_common::DynModule;

    let (_dir, path) = make_minimal_module();
    let loader = ModuleLoader::new();
    let module = loader.load(&path).expect("should load");

    let entry: Option<unsafe extern "C" fn()> = DynModule::entry_fn(&module);
    assert!(entry.is_some());
}

// ============== Registry Additional Tests ==============

#[test]
fn registry_unload_and_reload() {
    let (_dir, path) = make_minimal_module();
    let registry = ModuleRegistry::new();

    // Load module
    let first = registry.load(&path).unwrap();
    let first_ptr = Arc::as_ptr(&first);

    // Unload should succeed
    assert!(registry.unload(&path));

    // Unload again should fail (not in cache)
    assert!(!registry.unload(&path));

    // Load again - should get new instance
    let second = registry.load(&path).unwrap();
    let second_ptr = Arc::as_ptr(&second);

    // Should be different instances (not cached)
    assert_ne!(first_ptr, second_ptr);
}

#[test]
fn registry_reload_replaces_module() {
    let (_dir, path) = make_minimal_module();
    let registry = ModuleRegistry::new();

    // Load module
    let first = registry.load(&path).unwrap();
    let first_ptr = Arc::as_ptr(&first);

    // Reload
    let reloaded = registry.reload(&path).unwrap();
    let reloaded_ptr = Arc::as_ptr(&reloaded);

    // Should be different instances
    assert_ne!(first_ptr, reloaded_ptr);

    // Cache should have the reloaded version
    let cached = registry.load(&path).unwrap();
    assert!(Arc::ptr_eq(&reloaded, &cached));
}

#[test]
fn registry_resolve_symbol_finds_global() {
    let (_dir, path) = make_minimal_module();
    let registry = ModuleRegistry::new();

    // Before loading, symbol should not resolve
    assert!(registry.resolve_symbol("entry").is_none());

    // Load module
    let module = registry.load(&path).unwrap();

    // Now symbol should resolve
    let addr = registry.resolve_symbol("entry");
    assert!(addr.is_some());

    // Address should be within module's code memory
    let code_start = module.code_mem.as_ptr() as usize;
    let resolved = addr.unwrap();
    assert!(resolved >= code_start);
}

#[test]
fn registry_resolve_symbol_returns_none_for_unknown() {
    let (_dir, path) = make_minimal_module();
    let registry = ModuleRegistry::new();
    registry.load(&path).unwrap();

    // Unknown symbol should not resolve
    assert!(registry.resolve_symbol("nonexistent_symbol").is_none());
}

#[test]
fn registry_resolve_symbol_ignores_local_symbols() {
    let (_dir, path) = SmfBuilder::new("local.smf", "local_fn").local_symbol().build();

    let registry = ModuleRegistry::new();
    registry.load(&path).unwrap();

    // Local symbol should not be resolved by registry
    assert!(registry.resolve_symbol("local_fn").is_none());
}

#[test]
fn registry_load_nonexistent_fails() {
    let registry = ModuleRegistry::new();
    let result = registry.load(std::path::Path::new("/nonexistent/path.smf"));
    assert!(result.is_err());
}

#[test]
fn registry_unload_nonexistent_returns_false() {
    let registry = ModuleRegistry::new();
    assert!(!registry.unload(std::path::Path::new("/nonexistent/path.smf")));
}
