//! Package reader for loading SPK packages.

use std::fs::File;
use std::io::{Cursor, Read, Seek, SeekFrom};
use std::path::Path;

use super::format::*;
use super::writer::PackageError;

/// Loaded package information.
#[derive(Debug)]
pub struct LoadedPackage {
    /// Package trailer with section offsets
    pub trailer: PackageTrailer,
    /// Settlement data (SSMF bytes)
    pub settlement_data: Vec<u8>,
    /// Manifest section
    pub manifest: Option<ManifestSection>,
    /// Extracted resources
    pub resources: Vec<ResourceEntry>,
}

/// Package reader for loading SPK packages.
pub struct PackageReader;

impl PackageReader {
    /// Create a new package reader.
    pub fn new() -> Self {
        Self
    }

    /// Load a package from a file.
    pub fn load<P: AsRef<Path>>(&self, path: P) -> Result<LoadedPackage, PackageError> {
        let mut file = File::open(path)?;
        self.load_from_reader(&mut file)
    }

    /// Load a package from a byte slice.
    pub fn load_from_bytes(&self, bytes: &[u8]) -> Result<LoadedPackage, PackageError> {
        let mut cursor = Cursor::new(bytes);
        self.load_from_reader(&mut cursor)
    }

    /// Load a package from any seekable reader.
    pub fn load_from_reader<R: Read + Seek>(
        &self,
        reader: &mut R,
    ) -> Result<LoadedPackage, PackageError> {
        // Read trailer from end
        let trailer = PackageTrailer::read_from(reader)?;

        // Read settlement
        reader.seek(SeekFrom::Start(trailer.settlement_offset))?;
        let mut settlement_data = vec![0u8; trailer.settlement_size as usize];
        reader.read_exact(&mut settlement_data)?;

        // Verify settlement checksum
        if crc32(&settlement_data) != trailer.settlement_checksum {
            return Err(PackageError::InvalidSettlement);
        }

        // Read manifest if present
        let manifest = if trailer.has_manifest() && trailer.manifest_size > 0 {
            reader.seek(SeekFrom::Start(trailer.manifest_offset))?;
            let mut manifest_data = vec![0u8; trailer.manifest_size as usize];
            reader.read_exact(&mut manifest_data)?;
            ManifestSection::from_bytes(&manifest_data)
        } else {
            None
        };

        // Read resources if present
        let resources = if trailer.has_resources() && trailer.resources_size > 0 {
            reader.seek(SeekFrom::Start(trailer.resources_offset))?;
            let mut resources_data = vec![0u8; trailer.resources_size as usize];
            reader.read_exact(&mut resources_data)?;

            // Verify resources checksum
            if crc32(&resources_data) != trailer.resources_checksum {
                return Err(PackageError::CompressionError(
                    "Resources checksum mismatch".to_string(),
                ));
            }

            if trailer.resources_compressed() {
                self.decompress_resources(&resources_data)?
            } else {
                self.unpack_resources(&resources_data)?
            }
        } else {
            Vec::new()
        };

        Ok(LoadedPackage {
            trailer,
            settlement_data,
            manifest,
            resources,
        })
    }

    /// Load only the trailer (for quick inspection).
    pub fn load_trailer<P: AsRef<Path>>(&self, path: P) -> Result<PackageTrailer, PackageError> {
        let mut file = File::open(path)?;
        Ok(PackageTrailer::read_from(&mut file)?)
    }

    /// Load only the manifest (without loading full package).
    pub fn load_manifest<P: AsRef<Path>>(
        &self,
        path: P,
    ) -> Result<Option<ManifestSection>, PackageError> {
        let mut file = File::open(path)?;
        let trailer = PackageTrailer::read_from(&mut file)?;

        if !trailer.has_manifest() || trailer.manifest_size == 0 {
            return Ok(None);
        }

        file.seek(SeekFrom::Start(trailer.manifest_offset))?;
        let mut manifest_data = vec![0u8; trailer.manifest_size as usize];
        file.read_exact(&mut manifest_data)?;

        Ok(ManifestSection::from_bytes(&manifest_data))
    }

    /// Helper to read path from binary data
    fn read_path(data: &[u8], offset: &mut usize) -> Option<String> {
        if *offset + 2 > data.len() {
            return None;
        }
        let path_len = u16::from_le_bytes(data[*offset..*offset + 2].try_into().unwrap()) as usize;
        *offset += 2;

        if *offset + path_len > data.len() {
            return None;
        }
        let path = String::from_utf8_lossy(&data[*offset..*offset + path_len]).to_string();
        *offset += path_len;
        Some(path)
    }

    /// Read resource header (path and count)
    fn read_resource_header(data: &[u8], offset: &mut usize) -> Result<(usize, String), ()> {
        // Read path
        let path = match Self::read_path(data, offset) {
            Some(p) => p,
            None => return Err(()),
        };
        Ok((0, path))
    }

    /// Helper to read resource count and initialize parser
    fn init_resource_parser(data: &[u8]) -> Option<(Vec<ResourceEntry>, usize, usize)> {
        if data.len() < 4 {
            return None;
        }

        let resources = Vec::new();
        let offset = 0;

        // Read resource count
        let count = u32::from_le_bytes(data[offset..offset + 4].try_into().unwrap()) as usize;
        let offset = offset + 4;

        Some((resources, offset, count))
    }

    /// Helper to read resource path and advance offset
    fn read_resource_path(data: &[u8], offset: &mut usize) -> Option<String> {
        let (_, path) = Self::read_resource_header(data, offset).ok()?;
        Some(path)
    }

    /// Unpack resources without decompression.
    fn unpack_resources(&self, data: &[u8]) -> Result<Vec<ResourceEntry>, PackageError> {
        let (mut resources, mut offset, count) = match Self::init_resource_parser(data) {
            Some(result) => result,
            None => return Ok(Vec::new()),
        };

        for _ in 0..count {
            // Read path
            let path = match Self::read_resource_path(data, &mut offset) {
                Some(p) => p,
                None => break,
            };

            // Read data
            if offset + 4 > data.len() {
                break;
            }
            let data_len =
                u32::from_le_bytes(data[offset..offset + 4].try_into().unwrap()) as usize;
            offset += 4;

            if offset + data_len > data.len() {
                break;
            }
            let res_data = data[offset..offset + data_len].to_vec();
            offset += data_len;

            // Read checksum
            if offset + 4 > data.len() {
                break;
            }
            let checksum = u32::from_le_bytes(data[offset..offset + 4].try_into().unwrap());
            offset += 4;

            resources.push(ResourceEntry {
                path,
                data: res_data.clone(),
                uncompressed_size: res_data.len() as u32,
                checksum,
            });
        }

        Ok(resources)
    }

    /// Decompress resources.
    fn decompress_resources(&self, data: &[u8]) -> Result<Vec<ResourceEntry>, PackageError> {
        let (mut resources, mut offset, count) = match Self::init_resource_parser(data) {
            Some(result) => result,
            None => return Ok(Vec::new()),
        };

        for _ in 0..count {
            // Read path
            let path = match Self::read_resource_path(data, &mut offset) {
                Some(p) => p,
                None => break,
            };

            // Read compressed and uncompressed sizes
            if offset + 8 > data.len() {
                break;
            }
            let compressed_len =
                u32::from_le_bytes(data[offset..offset + 4].try_into().unwrap()) as usize;
            offset += 4;
            let uncompressed_size =
                u32::from_le_bytes(data[offset..offset + 4].try_into().unwrap());
            offset += 4;

            // Read compressed data
            if offset + compressed_len > data.len() {
                break;
            }
            let compressed_data = &data[offset..offset + compressed_len];
            offset += compressed_len;

            // Decompress
            let decompressed =
                self.simple_decompress(compressed_data, uncompressed_size as usize)?;

            // Read checksum
            if offset + 4 > data.len() {
                break;
            }
            let checksum = u32::from_le_bytes(data[offset..offset + 4].try_into().unwrap());
            offset += 4;

            // Verify checksum
            if crc32(&decompressed) != checksum {
                return Err(PackageError::CompressionError(format!(
                    "Checksum mismatch for resource: {}",
                    path
                )));
            }

            resources.push(ResourceEntry {
                path,
                data: decompressed,
                uncompressed_size,
                checksum,
            });
        }

        Ok(resources)
    }

    /// Simple decompression (inverse of simple_compress).
    fn simple_decompress(
        &self,
        data: &[u8],
        expected_size: usize,
    ) -> Result<Vec<u8>, PackageError> {
        if data.is_empty() {
            return Ok(Vec::new());
        }

        // Check for uncompressed marker
        if data[0] == 0xFE {
            if data.len() < 5 {
                return Err(PackageError::CompressionError(
                    "Invalid uncompressed data".to_string(),
                ));
            }
            let size = u32::from_le_bytes(data[1..5].try_into().unwrap()) as usize;
            if data.len() < 5 + size {
                return Err(PackageError::CompressionError(
                    "Truncated uncompressed data".to_string(),
                ));
            }
            return Ok(data[5..5 + size].to_vec());
        }

        let mut result = Vec::with_capacity(expected_size);
        let mut i = 0;

        while i < data.len() && result.len() < expected_size {
            let marker = data[i];
            i += 1;

            if marker == 0xFF {
                // RLE: count + byte
                if i + 2 > data.len() {
                    break;
                }
                let count = data[i] as usize;
                let byte = data[i + 1];
                i += 2;

                for _ in 0..count {
                    if result.len() >= expected_size {
                        break;
                    }
                    result.push(byte);
                }
            } else {
                // Literals
                let count = marker as usize;
                if i + count > data.len() {
                    break;
                }

                for j in 0..count {
                    if result.len() >= expected_size {
                        break;
                    }
                    result.push(data[i + j]);
                }
                i += count;
            }
        }

        if result.len() != expected_size {
            return Err(PackageError::CompressionError(format!(
                "Decompression size mismatch: got {}, expected {}",
                result.len(),
                expected_size
            )));
        }

        Ok(result)
    }
}

impl Default for PackageReader {
    fn default() -> Self {
        Self::new()
    }
}

/// Extract a specific resource from a package.
pub fn extract_resource<P: AsRef<Path>>(
    package_path: P,
    resource_path: &str,
) -> Result<Option<Vec<u8>>, PackageError> {
    let reader = PackageReader::new();
    let package = reader.load(package_path)?;

    for res in package.resources {
        if res.path == resource_path {
            return Ok(Some(res.data));
        }
    }

    Ok(None)
}

/// List all resources in a package.
pub fn list_resources<P: AsRef<Path>>(package_path: P) -> Result<Vec<String>, PackageError> {
    let reader = PackageReader::new();
    let package = reader.load(package_path)?;

    Ok(package.resources.into_iter().map(|r| r.path).collect())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_decompress_empty() {
        let reader = PackageReader::new();
        let result = reader.simple_decompress(&[], 0).unwrap();
        assert!(result.is_empty());
    }

    #[test]
    fn test_simple_decompress_uncompressed() {
        let reader = PackageReader::new();

        // Create uncompressed marker data
        let mut data = vec![0xFE];
        data.extend_from_slice(&5u32.to_le_bytes());
        data.extend_from_slice(b"hello");

        let result = reader.simple_decompress(&data, 5).unwrap();
        assert_eq!(result, b"hello");
    }

    #[test]
    fn test_decompress_rle() {
        let reader = PackageReader::new();

        // RLE encoded: 10 zeros
        let data = vec![0xFF, 10, 0x00];
        let result = reader.simple_decompress(&data, 10).unwrap();
        assert_eq!(result, vec![0u8; 10]);
    }

    #[test]
    fn test_decompress_literals() {
        let reader = PackageReader::new();

        // 5 literal bytes
        let data = vec![5, b'h', b'e', b'l', b'l', b'o'];
        let result = reader.simple_decompress(&data, 5).unwrap();
        assert_eq!(result, b"hello");
    }

    #[test]
    fn test_unpack_resources() {
        let reader = PackageReader::new();

        // Pack a simple resource manually
        let mut data = Vec::new();
        data.extend_from_slice(&1u32.to_le_bytes()); // count

        let path = b"test.txt";
        data.extend_from_slice(&(path.len() as u16).to_le_bytes());
        data.extend_from_slice(path);

        let content = b"test content";
        data.extend_from_slice(&(content.len() as u32).to_le_bytes());
        data.extend_from_slice(content);

        data.extend_from_slice(&crc32(content).to_le_bytes());

        let resources = reader.unpack_resources(&data).unwrap();
        assert_eq!(resources.len(), 1);
        assert_eq!(resources[0].path, "test.txt");
        assert_eq!(resources[0].data, content);
    }
}
