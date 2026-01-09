use std::io::Read;

use simple_common::target::{TargetArch, TargetOS};

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
    pub section_count: u32,
    pub section_table_offset: u64,

    pub symbol_table_offset: u64,
    pub symbol_count: u32,
    pub exported_count: u32,

    pub entry_point: u64,

    pub module_hash: u64,
    pub source_hash: u64,

    // Startup optimization hints (using reserved space)
    pub app_type: u8, // Application type (0=cli, 1=tui, 2=gui, 3=service, 4=repl)
    pub window_width: u16, // Window width hint (GUI apps)
    pub window_height: u16, // Window height hint (GUI apps)
    pub prefetch_hint: u8, // Prefetch hint: 0=no, 1=yes (#1998)
    pub prefetch_file_count: u8, // Expected number of files to prefetch
    pub reserved: [u8; 1], // Remaining reserved space
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

        // Safety: buffer is exactly the struct size and aligned enough for read.
        Ok(unsafe { std::ptr::read(buf.as_ptr() as *const SmfHeader) })
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

    /// Get the target architecture from the header.
    pub fn target_arch(&self) -> Option<TargetArch> {
        Arch::from_u8(self.arch).map(|a| a.to_target_arch())
    }

    /// Get the target platform/OS from the header.
    pub fn target_os(&self) -> Option<TargetOS> {
        Platform::from_u8(self.platform).map(|p| p.to_target_os())
    }

    /// Check if this SMF is compatible with the given architecture.
    pub fn is_compatible_arch(&self, arch: TargetArch) -> bool {
        self.target_arch().map_or(false, |a| a == arch)
    }

    /// Create a new header with the given architecture and platform.
    pub fn new_for_target(arch: TargetArch, os: TargetOS) -> Self {
        Self {
            magic: *SMF_MAGIC,
            version_major: 1,
            version_minor: 0,
            platform: Platform::from_target_os(os) as u8,
            arch: Arch::from_target_arch(arch) as u8,
            flags: 0,
            section_count: 0,
            section_table_offset: 0,
            symbol_table_offset: 0,
            symbol_count: 0,
            exported_count: 0,
            entry_point: 0,
            module_hash: 0,
            source_hash: 0,
            app_type: 0,        // Default to CLI
            window_width: 1280, // Default window size
            window_height: 720,
            prefetch_hint: 0, // No prefetch by default
            prefetch_file_count: 0,
            reserved: [0; 1],
        }
    }

    /// Get the application type from the header.
    pub fn get_app_type(&self) -> SmfAppType {
        SmfAppType::from_u8(self.app_type)
    }

    /// Set the application type in the header.
    pub fn set_app_type(&mut self, app_type: SmfAppType) {
        self.app_type = app_type as u8;
    }

    /// Set window hints for GUI applications.
    pub fn set_window_hints(&mut self, width: u16, height: u16) {
        self.window_width = width;
        self.window_height = height;
    }

    /// Enable prefetching and set expected file count (#1998).
    pub fn set_prefetch_hint(&mut self, enabled: bool, file_count: u8) {
        self.prefetch_hint = if enabled { 1 } else { 0 };
        self.prefetch_file_count = file_count;
    }

    /// Check if prefetching is recommended.
    pub fn should_prefetch(&self) -> bool {
        self.prefetch_hint != 0
    }

    /// Get the expected number of files to prefetch.
    pub fn expected_prefetch_count(&self) -> usize {
        self.prefetch_file_count as usize
    }
}

pub const SMF_FLAG_EXECUTABLE: u32 = 0x0001;
pub const SMF_FLAG_RELOADABLE: u32 = 0x0002;
pub const SMF_FLAG_DEBUG_INFO: u32 = 0x0004;
pub const SMF_FLAG_PIC: u32 = 0x0008;
pub const SMF_FLAG_COMPRESSED: u32 = 0x0010;

/// SMF platform identifier (maps to TargetOS).
#[derive(Debug, Clone, Copy, PartialEq)]
#[repr(u8)]
pub enum Platform {
    Any = 0,
    Linux = 1,
    Windows = 2,
    MacOS = 3,
    FreeBSD = 4,
    None = 5, // Bare metal
}

impl Platform {
    /// Convert from u8 value.
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

    /// Convert from TargetOS.
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

    /// Convert to TargetOS.
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

/// SMF architecture identifier (maps to TargetArch).
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
    /// Convert from u8 value.
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

    /// Convert from TargetArch.
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

    /// Convert to TargetArch.
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

    /// Check if this is a 32-bit architecture.
    pub fn is_32bit(self) -> bool {
        matches!(self, Arch::X86 | Arch::Arm | Arch::Riscv32 | Arch::Wasm32)
    }

    /// Check if this is a 64-bit architecture.
    pub fn is_64bit(self) -> bool {
        matches!(
            self,
            Arch::X86_64 | Arch::Aarch64 | Arch::Riscv64 | Arch::Wasm64
        )
    }
}

/// SMF application type identifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum SmfAppType {
    /// Command-line tool (minimal resources)
    Cli = 0,
    /// Terminal UI application (terminal mode, buffers)
    Tui = 1,
    /// Graphical application (window, GPU context)
    Gui = 2,
    /// Background service/daemon (IPC, signal handlers)
    Service = 3,
    /// Interactive REPL (history, line editor)
    Repl = 4,
}

impl SmfAppType {
    /// Convert from u8 value.
    pub fn from_u8(value: u8) -> Self {
        match value {
            1 => SmfAppType::Tui,
            2 => SmfAppType::Gui,
            3 => SmfAppType::Service,
            4 => SmfAppType::Repl,
            _ => SmfAppType::Cli, // Default to CLI for unknown values
        }
    }

    /// Convert to string name.
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

impl Default for SmfAppType {
    fn default() -> Self {
        SmfAppType::Cli
    }
}
