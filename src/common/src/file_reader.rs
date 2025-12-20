//! Memory-Mapped File Reading (#820)
//!
//! Provides efficient file reading using memory-mapped I/O for large files.
//! Falls back to regular reading for small files where mmap overhead isn't worth it.
//!
//! Expected impact: 15% faster file reading for large source files.

use memmap2::Mmap;
use std::fs::File;
use std::io::{self, Read};
use std::path::Path;

/// Threshold for using memory-mapped reading (files larger than this use mmap).
/// For small files, regular reading is faster due to mmap syscall overhead.
const MMAP_THRESHOLD: u64 = 32 * 1024; // 32 KB

/// File reading strategy.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReadStrategy {
    /// Always use regular file reading.
    Regular,
    /// Always use memory-mapped reading.
    Mmap,
    /// Automatically choose based on file size.
    Auto,
}

impl Default for ReadStrategy {
    fn default() -> Self {
        Self::Auto
    }
}

/// Read a file to a string using the specified strategy.
///
/// # Arguments
/// * `path` - The file path to read
/// * `strategy` - The reading strategy to use
///
/// # Returns
/// * `Ok(String)` - The file contents as a UTF-8 string
/// * `Err(io::Error)` - If the file cannot be read or is not valid UTF-8
pub fn read_to_string<P: AsRef<Path>>(path: P, strategy: ReadStrategy) -> io::Result<String> {
    let path = path.as_ref();
    let metadata = std::fs::metadata(path)?;
    let file_size = metadata.len();

    let use_mmap = match strategy {
        ReadStrategy::Regular => false,
        ReadStrategy::Mmap => true,
        ReadStrategy::Auto => file_size >= MMAP_THRESHOLD,
    };

    if use_mmap {
        read_to_string_mmap(path)
    } else {
        std::fs::read_to_string(path)
    }
}

/// Read a file to bytes using the specified strategy.
///
/// # Arguments
/// * `path` - The file path to read
/// * `strategy` - The reading strategy to use
///
/// # Returns
/// * `Ok(Vec<u8>)` - The file contents as bytes
/// * `Err(io::Error)` - If the file cannot be read
pub fn read_to_bytes<P: AsRef<Path>>(path: P, strategy: ReadStrategy) -> io::Result<Vec<u8>> {
    let path = path.as_ref();
    let metadata = std::fs::metadata(path)?;
    let file_size = metadata.len();

    let use_mmap = match strategy {
        ReadStrategy::Regular => false,
        ReadStrategy::Mmap => true,
        ReadStrategy::Auto => file_size >= MMAP_THRESHOLD,
    };

    if use_mmap {
        read_to_bytes_mmap(path)
    } else {
        std::fs::read(path)
    }
}

/// Read a file to string using memory mapping.
fn read_to_string_mmap<P: AsRef<Path>>(path: P) -> io::Result<String> {
    let file = File::open(path)?;

    // Safety: We're only reading the file, no concurrent modifications
    let mmap = unsafe { Mmap::map(&file)? };

    // Convert to string, validating UTF-8
    String::from_utf8(mmap.to_vec()).map_err(|e| {
        io::Error::new(io::ErrorKind::InvalidData, e)
    })
}

/// Read a file to bytes using memory mapping.
fn read_to_bytes_mmap<P: AsRef<Path>>(path: P) -> io::Result<Vec<u8>> {
    let file = File::open(path)?;

    // Safety: We're only reading the file, no concurrent modifications
    let mmap = unsafe { Mmap::map(&file)? };

    Ok(mmap.to_vec())
}

/// A memory-mapped file that can be used for zero-copy access.
/// Useful for parsing where you want to reference slices of the file.
pub struct MappedFile {
    _file: File,
    mmap: Mmap,
}

impl MappedFile {
    /// Open and memory-map a file.
    pub fn open<P: AsRef<Path>>(path: P) -> io::Result<Self> {
        let file = File::open(path)?;

        // Safety: We're only reading the file, no concurrent modifications
        let mmap = unsafe { Mmap::map(&file)? };

        Ok(Self { _file: file, mmap })
    }

    /// Get the file contents as a byte slice.
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        &self.mmap
    }

    /// Get the file contents as a string slice (if valid UTF-8).
    pub fn as_str(&self) -> Result<&str, std::str::Utf8Error> {
        std::str::from_utf8(&self.mmap)
    }

    /// Get the length of the file.
    #[inline]
    pub fn len(&self) -> usize {
        self.mmap.len()
    }

    /// Check if the file is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.mmap.is_empty()
    }
}

/// A simple file reader with configurable strategy.
/// Can be used as a drop-in replacement for `std::fs::read_to_string`.
pub struct FileReader {
    strategy: ReadStrategy,
}

impl FileReader {
    /// Create a new file reader with the given strategy.
    pub fn new(strategy: ReadStrategy) -> Self {
        Self { strategy }
    }

    /// Create a file reader that automatically chooses the best strategy.
    pub fn auto() -> Self {
        Self::new(ReadStrategy::Auto)
    }

    /// Read a file to string.
    pub fn read_to_string<P: AsRef<Path>>(&self, path: P) -> io::Result<String> {
        read_to_string(path, self.strategy)
    }

    /// Read a file to bytes.
    pub fn read_to_bytes<P: AsRef<Path>>(&self, path: P) -> io::Result<Vec<u8>> {
        read_to_bytes(path, self.strategy)
    }

    /// Open a file for zero-copy access (always uses mmap).
    pub fn open_mapped<P: AsRef<Path>>(&self, path: P) -> io::Result<MappedFile> {
        MappedFile::open(path)
    }
}

impl Default for FileReader {
    fn default() -> Self {
        Self::auto()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use tempfile::NamedTempFile;

    #[test]
    fn test_read_small_file() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(file, "Hello, World!").unwrap();

        let content = read_to_string(file.path(), ReadStrategy::Auto).unwrap();
        assert!(content.contains("Hello, World!"));
    }

    #[test]
    fn test_read_large_file_mmap() {
        let mut file = NamedTempFile::new().unwrap();
        // Write more than MMAP_THRESHOLD bytes
        let data = "x".repeat(64 * 1024);
        write!(file, "{}", data).unwrap();

        let content = read_to_string(file.path(), ReadStrategy::Mmap).unwrap();
        assert_eq!(content.len(), 64 * 1024);
    }

    #[test]
    fn test_mapped_file() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(file, "Test content").unwrap();

        let mapped = MappedFile::open(file.path()).unwrap();
        let content = mapped.as_str().unwrap();
        assert!(content.contains("Test content"));
    }

    #[test]
    fn test_file_reader() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(file, "Reader test").unwrap();

        let reader = FileReader::auto();
        let content = reader.read_to_string(file.path()).unwrap();
        assert!(content.contains("Reader test"));
    }
}
