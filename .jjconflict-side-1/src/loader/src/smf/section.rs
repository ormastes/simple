#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct SmfSection {
    pub section_type: SectionType,
    pub flags: u32,
    pub offset: u64,
    pub size: u64,
    pub virtual_size: u64,
    pub alignment: u64,
    pub name: [u8; 16],
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum SectionType {
    Code = 1,
    Data = 2,
    RoData = 3,
    Bss = 4,
    Reloc = 5,
    SymTab = 6,
    StrTab = 7,
    Debug = 8,
    TypeInfo = 9,
    Version = 10,
    SrcMap = 11,
}

impl SmfSection {
    pub fn name_str(&self) -> &str {
        let end = self
            .name
            .iter()
            .position(|&b| b == 0)
            .unwrap_or(self.name.len());
        std::str::from_utf8(&self.name[..end]).unwrap_or("")
    }

    pub fn is_executable(&self) -> bool {
        self.flags & SECTION_FLAG_EXEC != 0
    }

    pub fn is_writable(&self) -> bool {
        self.flags & SECTION_FLAG_WRITE != 0
    }
}

pub const SECTION_FLAG_READ: u32 = 0x01;
pub const SECTION_FLAG_WRITE: u32 = 0x02;
pub const SECTION_FLAG_EXEC: u32 = 0x04;
