use std::io::{Read, Seek, SeekFrom};

use crate::target::{TargetArch, TargetOS};

pub const SMF_MAGIC: &[u8; 4] = b"SMF\0";

#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct SmfHeader {
    pub magic: [u8; 4],
    pub version_major: u8,
    pub version_minor: u8,
    pub platform: u8,
    pub arch: u8,
    pub flags: u32,
    pub compression: u8,
    pub compression_level: u8,
    pub reserved_compression: [u8; 2],
    pub section_count: u32,
    pub section_table_offset: u64,
    pub symbol_table_offset: u64,
    pub symbol_count: u32,
    pub exported_count: u32,
    pub entry_point: u64,
    pub stub_size: u32,
    pub smf_data_offset: u32,
    pub module_hash: u64,
    pub source_hash: u64,
    pub app_type: u8,
    pub window_width: u16,
    pub window_height: u16,
    pub prefetch_hint: u8,
    pub prefetch_file_count: u8,
    pub reserved: [u8; 5],
}

impl SmfHeader {
    pub const SIZE: usize = std::mem::size_of::<Self>();

    pub fn read<R: Read>(reader: &mut R) -> std::io::Result<Self> {
        let mut buf = [0u8; Self::SIZE];
        reader.read_exact(&mut buf)?;

        if &buf[0..4] != SMF_MAGIC {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "Invalid SMF magic number",
            ));
        }

        Ok(unsafe { std::ptr::read(buf.as_ptr() as *const SmfHeader) })
    }

    pub fn read_trailer<R: Read + Seek>(reader: &mut R) -> std::io::Result<Self> {
        let current_pos = reader.stream_position()?;
        let file_size = reader.seek(SeekFrom::End(0))?;

        if file_size >= Self::SIZE as u64 {
            reader.seek(SeekFrom::Start(file_size - Self::SIZE as u64))?;
            let mut buf = [0u8; Self::SIZE];
            reader.read_exact(&mut buf)?;

            if &buf[0..4] == SMF_MAGIC {
                let header: SmfHeader = unsafe { std::ptr::read(buf.as_ptr() as *const SmfHeader) };
                return Ok(header);
            }
        }

        reader.seek(SeekFrom::Start(0))?;
        let mut buf = [0u8; Self::SIZE];
        reader.read_exact(&mut buf)?;

        if &buf[0..4] != SMF_MAGIC {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "Invalid SMF magic number (tried both v1.1 trailer and v1.0 header)",
            ));
        }

        let header: SmfHeader = unsafe { std::ptr::read(buf.as_ptr() as *const SmfHeader) };

        if current_pos != 0 && current_pos < file_size {
            reader.seek(SeekFrom::Start(Self::SIZE as u64))?;
        }

        Ok(header)
    }

    pub fn is_executable(&self) -> bool {
        self.flags & SMF_FLAG_EXECUTABLE != 0
    }

    pub fn is_reloadable(&self) -> bool {
        self.flags & SMF_FLAG_RELOADABLE != 0
    }

    pub fn has_debug_info(&self) -> bool {
        self.flags & SMF_FLAG_DEBUG_INFO != 0
    }

    pub fn target_arch(&self) -> Option<TargetArch> {
        Arch::from_u8(self.arch).map(|a| a.to_target_arch())
    }

    pub fn target_os(&self) -> Option<TargetOS> {
        Platform::from_u8(self.platform).map(|p| p.to_target_os())
    }

    pub fn is_compatible_arch(&self, arch: TargetArch) -> bool {
        self.target_arch() == Some(arch)
    }

    pub fn new_for_target(arch: TargetArch, os: TargetOS) -> Self {
        Self {
            magic: *SMF_MAGIC,
            version_major: 1,
            version_minor: 1,
            platform: Platform::from_target_os(os) as u8,
            arch: Arch::from_target_arch(arch) as u8,
            flags: 0,
            compression: 0,
            compression_level: 0,
            reserved_compression: [0; 2],
            section_count: 0,
            section_table_offset: 0,
            symbol_table_offset: 0,
            symbol_count: 0,
            exported_count: 0,
            entry_point: 0,
            stub_size: 0,
            smf_data_offset: 0,
            module_hash: 0,
            source_hash: 0,
            app_type: 0,
            window_width: 1280,
            window_height: 720,
            prefetch_hint: 0,
            prefetch_file_count: 0,
            reserved: [0; 5],
        }
    }

    pub fn get_app_type(&self) -> SmfAppType {
        SmfAppType::from_u8(self.app_type)
    }

    pub fn set_app_type(&mut self, app_type: SmfAppType) {
        self.app_type = app_type as u8;
    }

    pub fn set_window_hints(&mut self, width: u16, height: u16) {
        self.window_width = width;
        self.window_height = height;
    }

    pub fn set_prefetch_hint(&mut self, enabled: bool, file_count: u8) {
        self.prefetch_hint = if enabled { 1 } else { 0 };
        self.prefetch_file_count = file_count;
    }

    pub fn should_prefetch(&self) -> bool {
        self.prefetch_hint != 0
    }

    pub fn expected_prefetch_count(&self) -> usize {
        self.prefetch_file_count as usize
    }

    pub fn has_stub(&self) -> bool {
        self.flags & SMF_FLAG_HAS_STUB != 0
    }

    pub fn is_compressed(&self) -> bool {
        self.compression != 0
    }

    pub fn get_compression(&self) -> CompressionType {
        CompressionType::from_u8(self.compression)
    }

    pub fn set_compression(&mut self, compression: CompressionType, level: u8) {
        self.compression = compression as u8;
        self.compression_level = level;
    }

    pub fn get_stub_size(&self) -> u32 {
        self.stub_size
    }

    pub fn get_smf_data_offset(&self) -> u32 {
        self.smf_data_offset
    }

    pub fn set_stub_info(&mut self, stub_size: u32, smf_data_offset: u32) {
        self.stub_size = stub_size;
        self.smf_data_offset = smf_data_offset;
        if stub_size > 0 {
            self.flags |= SMF_FLAG_HAS_STUB;
        }
    }
}

pub const SMF_FLAG_EXECUTABLE: u32 = 0x0001;
pub const SMF_FLAG_RELOADABLE: u32 = 0x0002;
pub const SMF_FLAG_DEBUG_INFO: u32 = 0x0004;
pub const SMF_FLAG_PIC: u32 = 0x0008;
pub const SMF_FLAG_HAS_STUB: u32 = 0x0010;

#[derive(Debug, Clone, Copy, PartialEq)]
#[repr(u8)]
pub enum Platform {
    Any = 0,
    Linux = 1,
    Windows = 2,
    MacOS = 3,
    FreeBSD = 4,
    None = 5,
}

impl Platform {
    pub fn from_u8(value: u8) -> Option<Self> {
        match value {
            0 => Some(Platform::Any),
            1 => Some(Platform::Linux),
            2 => Some(Platform::Windows),
            3 => Some(Platform::MacOS),
            4 => Some(Platform::FreeBSD),
            5 => Some(Platform::None),
            _ => None,
        }
    }

    pub fn from_target_os(os: TargetOS) -> Self {
        match os {
            TargetOS::Any => Platform::Any,
            TargetOS::Linux => Platform::Linux,
            TargetOS::Windows => Platform::Windows,
            TargetOS::MacOS => Platform::MacOS,
            TargetOS::FreeBSD => Platform::FreeBSD,
            TargetOS::None => Platform::None,
        }
    }

    pub fn to_target_os(self) -> TargetOS {
        match self {
            Platform::Any => TargetOS::Any,
            Platform::Linux => TargetOS::Linux,
            Platform::Windows => TargetOS::Windows,
            Platform::MacOS => TargetOS::MacOS,
            Platform::FreeBSD => TargetOS::FreeBSD,
            Platform::None => TargetOS::None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
#[repr(u8)]
pub enum Arch {
    X86_64 = 0,
    Aarch64 = 1,
    X86 = 2,
    Arm = 3,
    Riscv64 = 4,
    Riscv32 = 5,
    Wasm32 = 6,
    Wasm64 = 7,
}

impl Arch {
    pub fn from_u8(value: u8) -> Option<Self> {
        match value {
            0 => Some(Arch::X86_64),
            1 => Some(Arch::Aarch64),
            2 => Some(Arch::X86),
            3 => Some(Arch::Arm),
            4 => Some(Arch::Riscv64),
            5 => Some(Arch::Riscv32),
            6 => Some(Arch::Wasm32),
            7 => Some(Arch::Wasm64),
            _ => None,
        }
    }

    pub fn from_target_arch(arch: TargetArch) -> Self {
        match arch {
            TargetArch::X86_64 => Arch::X86_64,
            TargetArch::Aarch64 => Arch::Aarch64,
            TargetArch::X86 => Arch::X86,
            TargetArch::Arm => Arch::Arm,
            TargetArch::Riscv64 => Arch::Riscv64,
            TargetArch::Riscv32 => Arch::Riscv32,
            TargetArch::Wasm32 => Arch::Wasm32,
            TargetArch::Wasm64 => Arch::Wasm64,
        }
    }

    pub fn to_target_arch(self) -> TargetArch {
        match self {
            Arch::X86_64 => TargetArch::X86_64,
            Arch::Aarch64 => TargetArch::Aarch64,
            Arch::X86 => TargetArch::X86,
            Arch::Arm => TargetArch::Arm,
            Arch::Riscv64 => TargetArch::Riscv64,
            Arch::Riscv32 => TargetArch::Riscv32,
            Arch::Wasm32 => TargetArch::Wasm32,
            Arch::Wasm64 => TargetArch::Wasm64,
        }
    }

    pub fn is_32bit(self) -> bool {
        matches!(self, Arch::X86 | Arch::Arm | Arch::Riscv32 | Arch::Wasm32)
    }

    pub fn is_64bit(self) -> bool {
        matches!(self, Arch::X86_64 | Arch::Aarch64 | Arch::Riscv64 | Arch::Wasm64)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
#[derive(Default)]
pub enum SmfAppType {
    #[default]
    Cli = 0,
    Tui = 1,
    Gui = 2,
    Service = 3,
    Repl = 4,
}

impl SmfAppType {
    pub fn from_u8(value: u8) -> Self {
        match value {
            1 => SmfAppType::Tui,
            2 => SmfAppType::Gui,
            3 => SmfAppType::Service,
            4 => SmfAppType::Repl,
            _ => SmfAppType::Cli,
        }
    }

    pub fn as_str(self) -> &'static str {
        match self {
            SmfAppType::Cli => "cli",
            SmfAppType::Tui => "tui",
            SmfAppType::Gui => "gui",
            SmfAppType::Service => "service",
            SmfAppType::Repl => "repl",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
#[derive(Default)]
pub enum CompressionType {
    #[default]
    None = 0,
    Zstd = 1,
    Lz4 = 2,
}

impl CompressionType {
    pub fn from_u8(value: u8) -> Self {
        match value {
            1 => CompressionType::Zstd,
            2 => CompressionType::Lz4,
            _ => CompressionType::None,
        }
    }

    pub fn as_str(self) -> &'static str {
        match self {
            CompressionType::None => "none",
            CompressionType::Zstd => "zstd",
            CompressionType::Lz4 => "lz4",
        }
    }
}
