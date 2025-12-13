//! Simple Package Format definitions.

use std::io::{Read, Seek, SeekFrom, Write};

/// Magic number for SPK format: "SPK1"
pub const SPK_MAGIC: [u8; 4] = *b"SPK1";

/// Current SPK format version
pub const SPK_VERSION: u16 = 1;

/// Size of the trailer (fixed, always at EOF - TRAILER_SIZE)
pub const TRAILER_SIZE: usize = std::mem::size_of::<PackageTrailer>();

/// Package flags
pub const SPK_FLAG_HAS_RESOURCES: u16 = 0x0001;
pub const SPK_FLAG_HAS_MANIFEST: u16 = 0x0002;
pub const SPK_FLAG_COMPRESSED_RESOURCES: u16 = 0x0004;
pub const SPK_FLAG_HAS_STDLIB: u16 = 0x0008;
pub const SPK_FLAG_STANDALONE: u16 = 0x0010; // All dependencies bundled

/// Package trailer - located at EOF - TRAILER_SIZE
///
/// This structure allows finding package sections by reading
/// from the end of the file, which works for both standalone
/// executables and appended packages.
#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct PackageTrailer {
    /// Offset to executable stub (always 0 for executables)
    pub stub_offset: u64,
    /// Size of executable stub
    pub stub_size: u64,

    /// Offset to SSMF settlement data
    pub settlement_offset: u64,
    /// Size of SSMF settlement
    pub settlement_size: u64,

    /// Offset to compressed resources (ZIP)
    pub resources_offset: u64,
    /// Size of compressed resources
    pub resources_size: u64,

    /// Offset to manifest section (uncompressed TOML)
    pub manifest_offset: u64,
    /// Size of manifest section
    pub manifest_size: u64,

    /// CRC32 of settlement section (for integrity)
    pub settlement_checksum: u32,
    /// CRC32 of resources section
    pub resources_checksum: u32,

    /// Package flags
    pub flags: u16,
    /// Format version
    pub version: u16,
    /// Magic number (must be SPK_MAGIC)
    pub magic: [u8; 4],
}

impl PackageTrailer {
    pub const SIZE: usize = std::mem::size_of::<Self>();

    /// Create a new trailer with magic and version set.
    pub fn new() -> Self {
        Self {
            magic: SPK_MAGIC,
            version: SPK_VERSION,
            ..Default::default()
        }
    }

    /// Check if magic number is valid.
    pub fn is_valid(&self) -> bool {
        self.magic == SPK_MAGIC
    }

    /// Check if package has compressed resources.
    pub fn has_resources(&self) -> bool {
        self.flags & SPK_FLAG_HAS_RESOURCES != 0
    }

    /// Check if package has manifest section.
    pub fn has_manifest(&self) -> bool {
        self.flags & SPK_FLAG_HAS_MANIFEST != 0
    }

    /// Check if resources are compressed.
    pub fn resources_compressed(&self) -> bool {
        self.flags & SPK_FLAG_COMPRESSED_RESOURCES != 0
    }

    /// Check if package includes stdlib.
    pub fn has_stdlib(&self) -> bool {
        self.flags & SPK_FLAG_HAS_STDLIB != 0
    }

    /// Check if package is standalone (all deps bundled).
    pub fn is_standalone(&self) -> bool {
        self.flags & SPK_FLAG_STANDALONE != 0
    }

    /// Read trailer from bytes.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() < Self::SIZE {
            return None;
        }

        // Read from end of slice
        let start = bytes.len() - Self::SIZE;
        let trailer_bytes = &bytes[start..];

        // Safety: PackageTrailer is repr(C) with only primitive types
        let trailer =
            unsafe { std::ptr::read_unaligned(trailer_bytes.as_ptr() as *const PackageTrailer) };

        if trailer.is_valid() {
            Some(trailer)
        } else {
            None
        }
    }

    /// Read trailer from a seekable reader.
    pub fn read_from<R: Read + Seek>(reader: &mut R) -> std::io::Result<Self> {
        // Seek to trailer position (EOF - TRAILER_SIZE)
        reader.seek(SeekFrom::End(-(Self::SIZE as i64)))?;

        let mut bytes = [0u8; Self::SIZE];
        reader.read_exact(&mut bytes)?;

        Self::from_bytes(&bytes).ok_or_else(|| {
            std::io::Error::new(std::io::ErrorKind::InvalidData, "Invalid package trailer")
        })
    }

    /// Write trailer to bytes.
    pub fn to_bytes(&self) -> [u8; Self::SIZE] {
        let mut bytes = [0u8; Self::SIZE];
        // Safety: PackageTrailer is repr(C) with only primitive types
        unsafe {
            std::ptr::write_unaligned(bytes.as_mut_ptr() as *mut PackageTrailer, *self);
        }
        bytes
    }

    /// Write trailer to writer.
    pub fn write_to<W: Write>(&self, writer: &mut W) -> std::io::Result<()> {
        writer.write_all(&self.to_bytes())
    }
}

/// Manifest section containing package metadata.
///
/// This is stored uncompressed so tools can inspect it without
/// loading the entire package.
#[derive(Debug, Clone, Default)]
pub struct ManifestSection {
    /// simple.toml content
    pub manifest_toml: String,
    /// simple.lock content (optional)
    pub lock_toml: Option<String>,
}

impl ManifestSection {
    /// Serialize to bytes with length prefixes.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut data = Vec::new();

        // Write manifest
        let manifest_bytes = self.manifest_toml.as_bytes();
        data.extend_from_slice(&(manifest_bytes.len() as u32).to_le_bytes());
        data.extend_from_slice(manifest_bytes);

        // Write lock (length 0 if none)
        if let Some(ref lock) = self.lock_toml {
            let lock_bytes = lock.as_bytes();
            data.extend_from_slice(&(lock_bytes.len() as u32).to_le_bytes());
            data.extend_from_slice(lock_bytes);
        } else {
            data.extend_from_slice(&0u32.to_le_bytes());
        }

        data
    }

    /// Parse from bytes.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() < 8 {
            return None;
        }

        let mut offset = 0;

        // Read manifest
        let manifest_len = u32::from_le_bytes(bytes[offset..offset + 4].try_into().ok()?) as usize;
        offset += 4;

        if offset + manifest_len > bytes.len() {
            return None;
        }

        let manifest_toml =
            String::from_utf8(bytes[offset..offset + manifest_len].to_vec()).ok()?;
        offset += manifest_len;

        // Read lock
        if offset + 4 > bytes.len() {
            return Some(Self {
                manifest_toml,
                lock_toml: None,
            });
        }

        let lock_len = u32::from_le_bytes(bytes[offset..offset + 4].try_into().ok()?) as usize;
        offset += 4;

        let lock_toml = if lock_len > 0 && offset + lock_len <= bytes.len() {
            Some(String::from_utf8(bytes[offset..offset + lock_len].to_vec()).ok()?)
        } else {
            None
        };

        Some(Self {
            manifest_toml,
            lock_toml,
        })
    }
}

/// Resource entry in the resources section.
#[derive(Debug, Clone)]
pub struct ResourceEntry {
    /// Path within package (e.g., "lib/std/core.spl")
    pub path: String,
    /// Compressed data
    pub data: Vec<u8>,
    /// Uncompressed size
    pub uncompressed_size: u32,
    /// CRC32 of uncompressed data
    pub checksum: u32,
}

/// Calculate CRC32 checksum.
pub fn crc32(data: &[u8]) -> u32 {
    // Simple CRC32 implementation (IEEE polynomial)
    const POLYNOMIAL: u32 = 0xEDB88320;

    let mut crc = 0xFFFFFFFF;
    for &byte in data {
        crc ^= byte as u32;
        for _ in 0..8 {
            if crc & 1 != 0 {
                crc = (crc >> 1) ^ POLYNOMIAL;
            } else {
                crc >>= 1;
            }
        }
    }
    !crc
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_trailer_size() {
        // Ensure trailer size is stable for binary compatibility
        assert!(PackageTrailer::SIZE >= 64);
        assert!(PackageTrailer::SIZE <= 128);
    }

    #[test]
    fn test_trailer_roundtrip() {
        let mut trailer = PackageTrailer::new();
        trailer.stub_size = 0x1000;
        trailer.settlement_offset = 0x1000;
        trailer.settlement_size = 0x5000;
        trailer.resources_offset = 0x6000;
        trailer.resources_size = 0x2000;
        trailer.flags = SPK_FLAG_HAS_RESOURCES | SPK_FLAG_COMPRESSED_RESOURCES;

        let bytes = trailer.to_bytes();

        // Prepend some data to simulate file content
        let mut file_data = vec![0u8; 0x10000];
        file_data.extend_from_slice(&bytes);

        let restored = PackageTrailer::from_bytes(&file_data).unwrap();

        assert!(restored.is_valid());
        assert_eq!(restored.stub_size, 0x1000);
        assert_eq!(restored.settlement_offset, 0x1000);
        assert_eq!(restored.settlement_size, 0x5000);
        assert!(restored.has_resources());
        assert!(restored.resources_compressed());
    }

    #[test]
    fn test_manifest_section() {
        let section = ManifestSection {
            manifest_toml: "[package]\nname = \"test\"".to_string(),
            lock_toml: Some("[[package]]\nname = \"dep\"".to_string()),
        };

        let bytes = section.to_bytes();
        let restored = ManifestSection::from_bytes(&bytes).unwrap();

        assert_eq!(restored.manifest_toml, section.manifest_toml);
        assert_eq!(restored.lock_toml, section.lock_toml);
    }

    #[test]
    fn test_manifest_section_no_lock() {
        let section = ManifestSection {
            manifest_toml: "[package]\nname = \"test\"".to_string(),
            lock_toml: None,
        };

        let bytes = section.to_bytes();
        let restored = ManifestSection::from_bytes(&bytes).unwrap();

        assert_eq!(restored.manifest_toml, section.manifest_toml);
        assert!(restored.lock_toml.is_none());
    }

    #[test]
    fn test_crc32() {
        // Test vector: "123456789" should give 0xCBF43926
        let data = b"123456789";
        assert_eq!(crc32(data), 0xCBF43926);
    }
}
