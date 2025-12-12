//! Teardown: Extract raw binaries from Settlement SMF for embedded targets.
//!
//! This module provides functionality to convert Settlement SSMF files
//! into raw binary images suitable for flashing to embedded devices.


/// Output format for teardown.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OutputFormat {
    /// Raw binary (direct memory image).
    RawBinary,
    /// Intel HEX format.
    IntelHex,
    /// Motorola S-Record format.
    SRecord,
}

/// Memory section in the output binary.
#[derive(Debug, Clone)]
pub struct MemorySection {
    /// Section name.
    pub name: &'static str,
    /// Load address (where to flash/load).
    pub load_addr: u32,
    /// Execution address (where code runs from).
    pub exec_addr: u32,
    /// Section data.
    pub data: &'static [u8],
    /// Section is executable.
    pub executable: bool,
    /// Section is writable.
    pub writable: bool,
}

/// Configuration for teardown operation.
#[derive(Debug, Clone, Copy)]
pub struct TeardownConfig {
    /// Target flash base address.
    pub flash_base: u32,
    /// Target RAM base address.
    pub ram_base: u32,
    /// Stack top address (usually end of RAM).
    pub stack_top: u32,
    /// Include vector table/startup code.
    pub include_startup: bool,
    /// Pad binary to alignment.
    pub alignment: u32,
    /// Fill byte for padding.
    pub fill_byte: u8,
}

impl Default for TeardownConfig {
    fn default() -> Self {
        Self {
            flash_base: 0x0800_0000,  // Common STM32 flash base
            ram_base: 0x2000_0000,    // Common Cortex-M RAM base
            stack_top: 0x2000_5000,   // 20KB RAM
            include_startup: true,
            alignment: 4,
            fill_byte: 0xFF,          // Flash erased state
        }
    }
}

/// Predefined configurations for common targets.
impl TeardownConfig {
    /// STM32F103 (Blue Pill) configuration.
    pub const fn stm32f103() -> Self {
        Self {
            flash_base: 0x0800_0000,
            ram_base: 0x2000_0000,
            stack_top: 0x2000_5000,  // 20KB RAM
            include_startup: true,
            alignment: 4,
            fill_byte: 0xFF,
        }
    }

    /// STM32F4xx configuration.
    pub const fn stm32f4() -> Self {
        Self {
            flash_base: 0x0800_0000,
            ram_base: 0x2000_0000,
            stack_top: 0x2002_0000,  // 128KB RAM
            include_startup: true,
            alignment: 4,
            fill_byte: 0xFF,
        }
    }

    /// nRF52832 configuration.
    pub const fn nrf52832() -> Self {
        Self {
            flash_base: 0x0000_0000,
            ram_base: 0x2000_0000,
            stack_top: 0x2001_0000,  // 64KB RAM
            include_startup: true,
            alignment: 4,
            fill_byte: 0xFF,
        }
    }

    /// ESP32-C3 (RISC-V) configuration.
    pub const fn esp32c3() -> Self {
        Self {
            flash_base: 0x4200_0000,
            ram_base: 0x3FC8_0000,
            stack_top: 0x3FCE_4000,  // 400KB RAM
            include_startup: true,
            alignment: 4,
            fill_byte: 0xFF,
        }
    }

    /// RISC-V QEMU virt configuration.
    pub const fn riscv_qemu() -> Self {
        Self {
            flash_base: 0x8000_0000,
            ram_base: 0x8800_0000,
            stack_top: 0x8810_0000,  // 1MB stack area
            include_startup: true,
            alignment: 4,
            fill_byte: 0x00,
        }
    }
}

/// Settlement header magic (SSMF).
pub const SSMF_MAGIC: [u8; 4] = *b"SSMF";

/// Minimal settlement header for parsing.
/// This mirrors the layout in src/loader/src/smf/settlement.rs
#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct SettlementHeaderMin {
    pub magic: [u8; 4],
    pub version: u16,
    pub flags: u16,
    pub arch: u8,
    pub reserved: [u8; 5],
    pub code_offset: u64,
    pub code_size: u64,
    pub data_offset: u64,
    pub data_size: u64,
    // We only need these fields for teardown
}

impl SettlementHeaderMin {
    pub const SIZE: usize = 16 + 32; // Basic fields + code/data offsets/sizes

    /// Check if magic is valid.
    pub fn is_valid(&self) -> bool {
        self.magic == SSMF_MAGIC
    }

    /// Parse header from bytes.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() < Self::SIZE {
            return None;
        }

        let mut header = Self::default();
        header.magic.copy_from_slice(&bytes[0..4]);
        header.version = u16::from_le_bytes([bytes[4], bytes[5]]);
        header.flags = u16::from_le_bytes([bytes[6], bytes[7]]);
        header.arch = bytes[8];
        header.reserved.copy_from_slice(&bytes[9..14]);

        // Skip to offset 16 for section info
        let offset = 16;
        header.code_offset = u64::from_le_bytes(bytes[offset..offset+8].try_into().ok()?);
        header.code_size = u64::from_le_bytes(bytes[offset+8..offset+16].try_into().ok()?);
        header.data_offset = u64::from_le_bytes(bytes[offset+16..offset+24].try_into().ok()?);
        header.data_size = u64::from_le_bytes(bytes[offset+24..offset+32].try_into().ok()?);

        if header.is_valid() {
            Some(header)
        } else {
            None
        }
    }
}

/// Result of teardown operation.
#[derive(Debug)]
pub struct TeardownResult {
    /// Code section (goes to flash).
    pub code: TeardownSection,
    /// Data section (initialized data, copied to RAM at startup).
    pub data: TeardownSection,
    /// Entry point address.
    pub entry_point: u32,
    /// Total binary size.
    pub total_size: usize,
}

/// A section extracted from settlement.
#[derive(Debug)]
pub struct TeardownSection {
    /// Load address.
    pub load_addr: u32,
    /// Size in bytes.
    pub size: usize,
    /// Offset in the output binary.
    pub offset: usize,
}

/// Intel HEX record type.
#[derive(Debug, Clone, Copy)]
#[repr(u8)]
pub enum HexRecordType {
    Data = 0x00,
    Eof = 0x01,
    ExtSegAddr = 0x02,
    StartSegAddr = 0x03,
    ExtLinAddr = 0x04,
    StartLinAddr = 0x05,
}

/// Generate Intel HEX output for a memory section.
///
/// # Arguments
/// * `data` - The data bytes
/// * `base_addr` - Base address for the data
/// * `output` - Output buffer (must be large enough)
///
/// Returns the number of bytes written to output.
pub fn generate_intel_hex(data: &[u8], base_addr: u32, output: &mut [u8]) -> usize {
    let mut out_idx = 0;
    let mut addr = base_addr;
    let mut current_ext_addr: u16 = (base_addr >> 16) as u16;

    // Write extended linear address record
    out_idx += write_hex_record(
        output,
        out_idx,
        HexRecordType::ExtLinAddr,
        0,
        &current_ext_addr.to_be_bytes(),
    );

    // Write data records (16 bytes per record)
    for chunk in data.chunks(16) {
        let new_ext_addr = (addr >> 16) as u16;
        if new_ext_addr != current_ext_addr {
            current_ext_addr = new_ext_addr;
            out_idx += write_hex_record(
                output,
                out_idx,
                HexRecordType::ExtLinAddr,
                0,
                &current_ext_addr.to_be_bytes(),
            );
        }

        let offset = (addr & 0xFFFF) as u16;
        out_idx += write_hex_record(
            output,
            out_idx,
            HexRecordType::Data,
            offset,
            chunk,
        );

        addr += chunk.len() as u32;
    }

    // Write EOF record
    out_idx += write_hex_record(output, out_idx, HexRecordType::Eof, 0, &[]);

    out_idx
}

/// Write a single Intel HEX record.
fn write_hex_record(
    output: &mut [u8],
    offset: usize,
    rec_type: HexRecordType,
    addr: u16,
    data: &[u8],
) -> usize {
    let mut idx = offset;

    // Start code
    output[idx] = b':';
    idx += 1;

    // Byte count
    idx += write_hex_byte(output, idx, data.len() as u8);

    // Address
    idx += write_hex_byte(output, idx, (addr >> 8) as u8);
    idx += write_hex_byte(output, idx, addr as u8);

    // Record type
    idx += write_hex_byte(output, idx, rec_type as u8);

    // Data
    let mut checksum: u8 = data.len() as u8;
    checksum = checksum.wrapping_add((addr >> 8) as u8);
    checksum = checksum.wrapping_add(addr as u8);
    checksum = checksum.wrapping_add(rec_type as u8);

    for &byte in data {
        idx += write_hex_byte(output, idx, byte);
        checksum = checksum.wrapping_add(byte);
    }

    // Checksum (two's complement)
    checksum = (!checksum).wrapping_add(1);
    idx += write_hex_byte(output, idx, checksum);

    // Line ending
    output[idx] = b'\r';
    output[idx + 1] = b'\n';
    idx += 2;

    idx - offset
}

/// Write a byte as two hex characters.
fn write_hex_byte(output: &mut [u8], offset: usize, byte: u8) -> usize {
    const HEX_CHARS: &[u8; 16] = b"0123456789ABCDEF";
    output[offset] = HEX_CHARS[(byte >> 4) as usize];
    output[offset + 1] = HEX_CHARS[(byte & 0x0F) as usize];
    2
}

/// Generate Motorola S-Record output.
pub fn generate_srec(data: &[u8], base_addr: u32, entry_point: u32, output: &mut [u8]) -> usize {
    let mut out_idx = 0;

    // S0 header record
    let header = b"SIMPLE";
    out_idx += write_srec_record(output, out_idx, b'0', 0, header);

    // S3 data records (32-bit address)
    let mut addr = base_addr;
    for chunk in data.chunks(16) {
        out_idx += write_srec_record(output, out_idx, b'3', addr, chunk);
        addr += chunk.len() as u32;
    }

    // S7 end record (32-bit start address)
    out_idx += write_srec_record(output, out_idx, b'7', entry_point, &[]);

    out_idx
}

/// Write a single S-Record.
fn write_srec_record(output: &mut [u8], offset: usize, rec_type: u8, addr: u32, data: &[u8]) -> usize {
    let mut idx = offset;

    // Start code
    output[idx] = b'S';
    output[idx + 1] = rec_type;
    idx += 2;

    // Calculate byte count: address + data + checksum
    let addr_len = if rec_type == b'0' || rec_type == b'1' || rec_type == b'9' {
        2
    } else if rec_type == b'2' || rec_type == b'8' {
        3
    } else {
        4
    };
    let byte_count = addr_len + data.len() + 1;

    idx += write_hex_byte(output, idx, byte_count as u8);

    // Address
    let mut checksum: u8 = byte_count as u8;
    if addr_len >= 4 {
        idx += write_hex_byte(output, idx, (addr >> 24) as u8);
        checksum = checksum.wrapping_add((addr >> 24) as u8);
    }
    if addr_len >= 3 {
        idx += write_hex_byte(output, idx, (addr >> 16) as u8);
        checksum = checksum.wrapping_add((addr >> 16) as u8);
    }
    idx += write_hex_byte(output, idx, (addr >> 8) as u8);
    checksum = checksum.wrapping_add((addr >> 8) as u8);
    idx += write_hex_byte(output, idx, addr as u8);
    checksum = checksum.wrapping_add(addr as u8);

    // Data
    for &byte in data {
        idx += write_hex_byte(output, idx, byte);
        checksum = checksum.wrapping_add(byte);
    }

    // Checksum (one's complement)
    checksum = !checksum;
    idx += write_hex_byte(output, idx, checksum);

    // Line ending
    output[idx] = b'\r';
    output[idx + 1] = b'\n';
    idx += 2;

    idx - offset
}

/// Calculate required output buffer size for Intel HEX.
pub const fn intel_hex_size(data_len: usize) -> usize {
    // Each 16-byte chunk becomes ~45 bytes in hex
    // Plus extended address records and EOF
    let num_records = (data_len + 15) / 16;
    let ext_addr_records = (data_len + 65535) / 65536;
    (num_records + ext_addr_records + 1) * 48
}

/// Calculate required output buffer size for S-Record.
pub const fn srec_size(data_len: usize) -> usize {
    // Each 16-byte chunk becomes ~48 bytes in srec
    // Plus header and end records
    let num_records = (data_len + 15) / 16;
    (num_records + 2) * 52
}

/// Align a value up to the given alignment.
pub const fn align_up(value: u32, alignment: u32) -> u32 {
    (value + alignment - 1) & !(alignment - 1)
}

/// ARM Cortex-M vector table entry point extraction.
/// The vector table starts with stack pointer, then reset handler.
pub fn extract_cortex_m_entry(code: &[u8]) -> Option<u32> {
    if code.len() < 8 {
        return None;
    }
    // Reset handler is at offset 4 (second word)
    Some(u32::from_le_bytes([code[4], code[5], code[6], code[7]]))
}

/// RISC-V entry point is typically at the start of code.
pub fn extract_riscv_entry(_code: &[u8], base_addr: u32) -> u32 {
    // Entry is at base address for RISC-V
    base_addr
}
