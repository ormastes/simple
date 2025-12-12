//! Package writer for creating SPK packages.

use std::fs::File;
use std::io::{self, Cursor, Read, Seek, SeekFrom, Write};
use std::path::Path;

use crate::settlement::{BuildOptions, Settlement, SettlementBuilder};
use super::format::*;

/// Error type for package operations.
#[derive(Debug)]
pub enum PackageError {
    IoError(io::Error),
    InvalidStub,
    InvalidSettlement,
    CompressionError(String),
    MissingManifest,
}

impl std::fmt::Display for PackageError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PackageError::IoError(e) => write!(f, "I/O error: {}", e),
            PackageError::InvalidStub => write!(f, "Invalid executable stub"),
            PackageError::InvalidSettlement => write!(f, "Invalid settlement data"),
            PackageError::CompressionError(msg) => write!(f, "Compression error: {}", msg),
            PackageError::MissingManifest => write!(f, "Missing package manifest"),
        }
    }
}

impl std::error::Error for PackageError {}

impl From<io::Error> for PackageError {
    fn from(e: io::Error) -> Self {
        PackageError::IoError(e)
    }
}

/// Options for building a package.
#[derive(Debug, Clone)]
pub struct PackageOptions {
    /// Include executable stub (create standalone executable)
    pub executable: bool,
    /// Path to executable stub
    pub stub_path: Option<std::path::PathBuf>,
    /// Compress resources
    pub compress_resources: bool,
    /// Compression level (0-9)
    pub compression_level: u8,
    /// Include stdlib in package
    pub include_stdlib: bool,
    /// Bundle all dependencies
    pub standalone: bool,
    /// Target architecture
    pub arch: u8,
}

impl Default for PackageOptions {
    fn default() -> Self {
        Self {
            executable: false,
            stub_path: None,
            compress_resources: true,
            compression_level: 6,
            include_stdlib: false,
            standalone: false,
            arch: BuildOptions::current_arch(),
        }
    }
}

impl PackageOptions {
    /// Create options for a standalone executable.
    pub fn executable() -> Self {
        Self {
            executable: true,
            standalone: true,
            ..Default::default()
        }
    }

    /// Create options for a library package.
    pub fn library() -> Self {
        Self {
            executable: false,
            standalone: false,
            ..Default::default()
        }
    }
}

/// Builder for creating SPK packages.
pub struct PackageWriter {
    options: PackageOptions,
}

impl PackageWriter {
    /// Create a new package writer.
    pub fn new() -> Self {
        Self {
            options: PackageOptions::default(),
        }
    }

    /// Create with specific options.
    pub fn with_options(options: PackageOptions) -> Self {
        Self { options }
    }

    /// Build a package from a settlement.
    pub fn build<W: Write + Seek>(
        &self,
        settlement: &Settlement,
        manifest: &ManifestSection,
        resources: &[ResourceEntry],
        output: &mut W,
    ) -> Result<(), PackageError> {
        let mut trailer = PackageTrailer::new();

        // Track current position
        let mut current_pos = 0u64;

        // 1. Write executable stub (if creating executable)
        trailer.stub_offset = current_pos;
        if self.options.executable {
            let stub_data = self.get_stub_data()?;
            output.write_all(&stub_data)?;
            trailer.stub_size = stub_data.len() as u64;
            current_pos += trailer.stub_size;
        } else {
            trailer.stub_size = 0;
        }

        // 2. Write settlement (SSMF format)
        trailer.settlement_offset = current_pos;
        let settlement_data = self.serialize_settlement(settlement)?;
        trailer.settlement_checksum = crc32(&settlement_data);
        output.write_all(&settlement_data)?;
        trailer.settlement_size = settlement_data.len() as u64;
        current_pos += trailer.settlement_size;

        // 3. Write resources (optionally compressed)
        trailer.resources_offset = current_pos;
        if !resources.is_empty() {
            trailer.flags |= SPK_FLAG_HAS_RESOURCES;

            let resources_data = if self.options.compress_resources {
                trailer.flags |= SPK_FLAG_COMPRESSED_RESOURCES;
                self.compress_resources(resources)?
            } else {
                self.pack_resources(resources)?
            };

            trailer.resources_checksum = crc32(&resources_data);
            output.write_all(&resources_data)?;
            trailer.resources_size = resources_data.len() as u64;
            current_pos += trailer.resources_size;
        } else {
            trailer.resources_size = 0;
        }

        // 4. Write manifest section (uncompressed)
        trailer.manifest_offset = current_pos;
        let manifest_data = manifest.to_bytes();
        if !manifest_data.is_empty() {
            trailer.flags |= SPK_FLAG_HAS_MANIFEST;
            output.write_all(&manifest_data)?;
            trailer.manifest_size = manifest_data.len() as u64;
            current_pos += trailer.manifest_size;
        } else {
            trailer.manifest_size = 0;
        }

        // 5. Set remaining flags
        if self.options.include_stdlib {
            trailer.flags |= SPK_FLAG_HAS_STDLIB;
        }
        if self.options.standalone {
            trailer.flags |= SPK_FLAG_STANDALONE;
        }

        // 6. Write trailer
        trailer.write_to(output)?;

        Ok(())
    }

    /// Build a package to a file.
    pub fn build_to_file<P: AsRef<Path>>(
        &self,
        settlement: &Settlement,
        manifest: &ManifestSection,
        resources: &[ResourceEntry],
        output_path: P,
    ) -> Result<(), PackageError> {
        let mut file = File::create(output_path)?;
        self.build(settlement, manifest, resources, &mut file)?;

        // Make executable on Unix
        #[cfg(unix)]
        if self.options.executable {
            use std::os::unix::fs::PermissionsExt;
            let mut perms = file.metadata()?.permissions();
            perms.set_mode(0o755);
            file.set_permissions(perms)?;
        }

        Ok(())
    }

    /// Build a package to a byte vector.
    pub fn build_to_vec(
        &self,
        settlement: &Settlement,
        manifest: &ManifestSection,
        resources: &[ResourceEntry],
    ) -> Result<Vec<u8>, PackageError> {
        let mut buffer = Cursor::new(Vec::new());
        self.build(settlement, manifest, resources, &mut buffer)?;
        Ok(buffer.into_inner())
    }

    /// Get executable stub data.
    fn get_stub_data(&self) -> Result<Vec<u8>, PackageError> {
        if let Some(ref stub_path) = self.options.stub_path {
            let mut file = File::open(stub_path)?;
            let mut data = Vec::new();
            file.read_to_end(&mut data)?;
            Ok(data)
        } else {
            // Try to find the stub automatically
            if let Some(stub_path) = crate::settlement::find_stub() {
                let mut file = File::open(stub_path)?;
                let mut data = Vec::new();
                file.read_to_end(&mut data)?;
                Ok(data)
            } else {
                Err(PackageError::InvalidStub)
            }
        }
    }

    /// Serialize settlement to SSMF bytes.
    fn serialize_settlement(&self, settlement: &Settlement) -> Result<Vec<u8>, PackageError> {
        let builder = SettlementBuilder::with_options(BuildOptions {
            executable: false, // We handle the stub separately
            stub_path: None,
            arch: self.options.arch,
            debug_info: false,
            compression: 0,
        });

        builder.build_to_vec(settlement)
            .map_err(|_| PackageError::InvalidSettlement)
    }

    /// Pack resources without compression.
    fn pack_resources(&self, resources: &[ResourceEntry]) -> Result<Vec<u8>, PackageError> {
        let mut data = Vec::new();

        // Write resource count
        data.extend_from_slice(&(resources.len() as u32).to_le_bytes());

        // Write each resource
        for res in resources {
            // Path length and path
            let path_bytes = res.path.as_bytes();
            data.extend_from_slice(&(path_bytes.len() as u16).to_le_bytes());
            data.extend_from_slice(path_bytes);

            // Data length and data
            data.extend_from_slice(&(res.data.len() as u32).to_le_bytes());
            data.extend_from_slice(&res.data);

            // Checksum
            data.extend_from_slice(&res.checksum.to_le_bytes());
        }

        Ok(data)
    }

    /// Compress resources using simple LZ compression.
    ///
    /// Format: resource_count (u32) + [path_len (u16) + path + compressed_len (u32) +
    ///         uncompressed_len (u32) + compressed_data + checksum (u32)]
    fn compress_resources(&self, resources: &[ResourceEntry]) -> Result<Vec<u8>, PackageError> {
        let mut data = Vec::new();

        // Write resource count
        data.extend_from_slice(&(resources.len() as u32).to_le_bytes());

        // Write each resource
        for res in resources {
            // Path
            let path_bytes = res.path.as_bytes();
            data.extend_from_slice(&(path_bytes.len() as u16).to_le_bytes());
            data.extend_from_slice(path_bytes);

            // Compress data using simple RLE + LZ77-lite
            let compressed = self.simple_compress(&res.data);

            // Sizes
            data.extend_from_slice(&(compressed.len() as u32).to_le_bytes());
            data.extend_from_slice(&res.uncompressed_size.to_le_bytes());

            // Compressed data
            data.extend_from_slice(&compressed);

            // Checksum of uncompressed data
            data.extend_from_slice(&res.checksum.to_le_bytes());
        }

        Ok(data)
    }

    /// Simple compression using RLE for repeated bytes.
    /// Format: [literal_count (1 byte) + literals...] or [0xFF + repeat_count (1 byte) + byte]
    fn simple_compress(&self, data: &[u8]) -> Vec<u8> {
        if data.is_empty() {
            return Vec::new();
        }

        let mut result = Vec::with_capacity(data.len());
        let mut i = 0;

        while i < data.len() {
            // Check for run of same byte
            let mut run_len = 1;
            while i + run_len < data.len()
                && data[i + run_len] == data[i]
                && run_len < 255
            {
                run_len += 1;
            }

            if run_len >= 4 {
                // Encode as RLE: marker + count + byte
                result.push(0xFF);
                result.push(run_len as u8);
                result.push(data[i]);
                i += run_len;
            } else {
                // Collect literals
                let mut literal_start = i;
                let mut literal_count = 0;

                while i < data.len() && literal_count < 254 {
                    // Check if next position starts a good run
                    let mut next_run = 1;
                    while i + next_run < data.len()
                        && data[i + next_run] == data[i]
                        && next_run < 255
                    {
                        next_run += 1;
                    }

                    if next_run >= 4 {
                        break;
                    }

                    literal_count += 1;
                    i += 1;
                }

                if literal_count > 0 {
                    result.push(literal_count as u8);
                    result.extend_from_slice(&data[literal_start..literal_start + literal_count]);
                }
            }
        }

        // If compression didn't help, return original with marker
        if result.len() >= data.len() {
            let mut uncompressed = vec![0xFE]; // Uncompressed marker
            uncompressed.extend_from_slice(&(data.len() as u32).to_le_bytes());
            uncompressed.extend_from_slice(data);
            uncompressed
        } else {
            result
        }
    }
}

impl Default for PackageWriter {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_package_options_default() {
        let opts = PackageOptions::default();
        assert!(!opts.executable);
        assert!(opts.compress_resources);
    }

    #[test]
    fn test_package_options_executable() {
        let opts = PackageOptions::executable();
        assert!(opts.executable);
        assert!(opts.standalone);
    }

    #[test]
    fn test_simple_compress_literals() {
        let writer = PackageWriter::new();
        let data = b"hello world";
        let compressed = writer.simple_compress(data);
        // Should either compress or return with uncompressed marker
        assert!(!compressed.is_empty());
    }

    #[test]
    fn test_simple_compress_run() {
        let writer = PackageWriter::new();
        let data = vec![0u8; 100];
        let compressed = writer.simple_compress(&data);
        // Should compress well due to runs
        assert!(compressed.len() < data.len());
    }

    #[test]
    fn test_pack_resources() {
        let writer = PackageWriter::new();
        let resources = vec![
            ResourceEntry {
                path: "lib/test.spl".to_string(),
                data: b"test data".to_vec(),
                uncompressed_size: 9,
                checksum: crc32(b"test data"),
            },
        ];

        let packed = writer.pack_resources(&resources).unwrap();
        assert!(!packed.is_empty());

        // Verify structure: count (4) + path_len (2) + path (12) + data_len (4) + data (9) + checksum (4) = 35
        assert!(packed.len() >= 35);
    }
}
