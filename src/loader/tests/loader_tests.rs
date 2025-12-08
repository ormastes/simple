use std::io::Cursor;
use std::sync::Arc;

use simple_loader::loader::ModuleLoader;
use simple_loader::registry::ModuleRegistry;
use simple_loader::smf::{
    apply_relocations, hash_name, Arch, Platform, RelocationType, SectionType, SmfHeader,
    SmfRelocation, SmfSection, SmfSymbol, SymbolBinding, SymbolTable, SymbolType,
    SMF_FLAG_EXECUTABLE, SMF_MAGIC, SECTION_FLAG_EXEC, SECTION_FLAG_READ,
};

fn push_struct<T: Copy>(buf: &mut Vec<u8>, value: &T) {
    let slice =
        unsafe { std::slice::from_raw_parts(value as *const T as *const u8, std::mem::size_of::<T>()) };
    buf.extend_from_slice(slice);
}

fn make_minimal_module() -> (tempfile::TempDir, std::path::PathBuf) {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("module.smf");

    let section_table_offset = SmfHeader::SIZE as u64;
    let section_table_size = std::mem::size_of::<SmfSection>() as u64;
    let code_offset = section_table_offset + section_table_size;
    let code_bytes = vec![0xC3u8]; // ret
    let symbol_table_offset = code_offset + code_bytes.len() as u64;

    let mut header = SmfHeader {
        magic: *SMF_MAGIC,
        version_major: 0,
        version_minor: 1,
        platform: Platform::Any as u8,
        arch: Arch::X86_64 as u8,
        flags: SMF_FLAG_EXECUTABLE,
        section_count: 1,
        section_table_offset,
        symbol_table_offset,
        symbol_count: 1,
        exported_count: 1,
        entry_point: 0,
        module_hash: 0,
        source_hash: 0,
        reserved: [0; 8],
    };

    let mut name = [0u8; 16];
    name[..4].copy_from_slice(b"code");
    let code_section = SmfSection {
        section_type: SectionType::Code,
        flags: SECTION_FLAG_READ | SECTION_FLAG_EXEC,
        offset: code_offset,
        size: code_bytes.len() as u64,
        virtual_size: code_bytes.len() as u64,
        alignment: 16,
        name,
    };

    let string_table = b"entry\0".to_vec();
    let symbol = SmfSymbol {
        name_offset: 0,
        name_hash: hash_name("entry"),
        sym_type: SymbolType::Function,
        binding: SymbolBinding::Global,
        visibility: 0,
        flags: 0,
        value: 0,
        size: 0,
        type_id: 0,
        version: 0,
    };

    header.symbol_table_offset = symbol_table_offset;

    let mut buf = Vec::new();
    push_struct(&mut buf, &header);
    push_struct(&mut buf, &code_section);
    buf.extend_from_slice(&code_bytes);
    push_struct(&mut buf, &symbol);
    buf.extend_from_slice(&string_table);

    std::fs::write(&path, &buf).unwrap();
    (dir, path)
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
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join(format!("{name}.smf"));

    let section_table_offset = SmfHeader::SIZE as u64;
    let section_table_size = std::mem::size_of::<SmfSection>() as u64;
    let code_offset = section_table_offset + section_table_size;
    let code_bytes = vec![0xC3u8]; // ret
    let symbol_table_offset = code_offset + code_bytes.len() as u64;

    let mut header = SmfHeader {
        magic: *SMF_MAGIC,
        version_major: 0,
        version_minor: 1,
        platform: Platform::Any as u8,
        arch: Arch::X86_64 as u8,
        flags: SMF_FLAG_EXECUTABLE,
        section_count: 1,
        section_table_offset,
        symbol_table_offset,
        symbol_count: 1,
        exported_count: 1,
        entry_point: 0,
        module_hash: 0,
        source_hash: 0,
        reserved: [0; 8],
    };

    let mut sec_name = [0u8; 16];
    sec_name[..4].copy_from_slice(b"code");
    let code_section = SmfSection {
        section_type: SectionType::Code,
        flags: SECTION_FLAG_READ | SECTION_FLAG_EXEC,
        offset: code_offset,
        size: code_bytes.len() as u64,
        virtual_size: code_bytes.len() as u64,
        alignment: 16,
        name: sec_name,
    };

    let string_table = format!("{name}\0").into_bytes();
    let symbol = SmfSymbol {
        name_offset: 0,
        name_hash: hash_name(name),
        sym_type: SymbolType::Function,
        binding: SymbolBinding::Global,
        visibility: 0,
        flags: 0,
        value: 0,
        size: 0,
        type_id: 0,
        version: 0,
    };

    header.symbol_table_offset = symbol_table_offset;

    let mut buf = Vec::new();
    push_struct(&mut buf, &header);
    push_struct(&mut buf, &code_section);
    buf.extend_from_slice(&code_bytes);
    push_struct(&mut buf, &symbol);
    buf.extend_from_slice(&string_table);

    std::fs::write(&path, &buf).unwrap();
    (dir, path)
}

fn make_importing_module(import_name: &str) -> (tempfile::TempDir, std::path::PathBuf) {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("importer.smf");

    let section_table_offset = SmfHeader::SIZE as u64;
    let section_table_size = std::mem::size_of::<SmfSection>() as u64;

    // Layout: header | sections | code | reloc | symbols | strings
    let code_offset = section_table_offset + section_table_size * 2;
    let code_bytes = vec![0u8; 8]; // will be patched

    let reloc_offset = code_offset + code_bytes.len() as u64;
    let reloc_size = std::mem::size_of::<SmfRelocation>() as u64;
    let symbol_table_offset = reloc_offset + reloc_size;

    let mut header = SmfHeader {
        magic: *SMF_MAGIC,
        version_major: 0,
        version_minor: 1,
        platform: Platform::Any as u8,
        arch: Arch::X86_64 as u8,
        flags: SMF_FLAG_EXECUTABLE,
        section_count: 2,
        section_table_offset,
        symbol_table_offset,
        symbol_count: 1,
        exported_count: 0,
        entry_point: 0,
        module_hash: 0,
        source_hash: 0,
        reserved: [0; 8],
    };

    let mut code_name = [0u8; 16];
    code_name[..4].copy_from_slice(b"code");
    let code_section = SmfSection {
        section_type: SectionType::Code,
        flags: SECTION_FLAG_READ | SECTION_FLAG_EXEC,
        offset: code_offset,
        size: code_bytes.len() as u64,
        virtual_size: code_bytes.len() as u64,
        alignment: 16,
        name: code_name,
    };

    let mut reloc_name = [0u8; 16];
    reloc_name[..5].copy_from_slice(b"reloc");
    let reloc_section = SmfSection {
        section_type: SectionType::Reloc,
        flags: SECTION_FLAG_READ,
        offset: reloc_offset,
        size: reloc_size,
        virtual_size: reloc_size,
        alignment: 8,
        name: reloc_name,
    };

    let string_table = format!("{import_name}\0").into_bytes();
    let symbol = SmfSymbol {
        name_offset: 0,
        name_hash: hash_name(import_name),
        sym_type: SymbolType::Function,
        binding: SymbolBinding::Global,
        visibility: 0,
        flags: 0,
        value: 0,
        size: 0,
        type_id: 0,
        version: 0,
    };

    let reloc = SmfRelocation {
        offset: 0,
        symbol_index: 0,
        reloc_type: RelocationType::Abs64,
        addend: 0,
    };

    header.symbol_table_offset = symbol_table_offset;

    let mut buf = Vec::new();
    push_struct(&mut buf, &header);
    push_struct(&mut buf, &code_section);
    push_struct(&mut buf, &reloc_section);
    buf.extend_from_slice(&code_bytes);
    push_struct(&mut buf, &reloc);
    push_struct(&mut buf, &symbol);
    buf.extend_from_slice(&string_table);

    std::fs::write(&path, &buf).unwrap();
    (dir, path)
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
