//! Hot-reload support for note.sdn section.
//!
//! This module provides functionality to update the note.sdn section
//! in SMF files without modifying the section table, enabling:
//! - Runtime updates after JIT compilation
//! - Incremental updates during development
//! - Cache invalidation signaling
//!
//! Phase 7: Hot-Reload Support

use std::fs::{File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
use std::path::Path;

use super::note_sdn::{NoteSdnMetadata, InstantiationEntry, InstantiationStatus};

/// The terminator that marks the end of note.sdn data.
pub const NOTE_SDN_TERMINATOR: &str = "\n# END_NOTE\n";

/// Result of a hot-reload operation.
#[derive(Debug)]
pub enum HotReloadResult {
    /// Successfully updated note.sdn in place
    Success,
    /// Data too large, need full SMF rebuild
    NeedRebuild {
        /// Current data size
        current_size: usize,
        /// Required data size
        required_size: usize,
        /// Available space
        available_space: usize,
    },
    /// SMF file not found or invalid
    InvalidSmf {
        /// Error message
        message: String,
    },
    /// I/O error during update
    IoError {
        /// Error message
        message: String,
    },
}

/// Configuration for hot-reload operations.
#[derive(Debug, Clone)]
pub struct HotReloadConfig {
    /// Create backup before update
    pub create_backup: bool,
    /// Verify update after write
    pub verify_after_write: bool,
    /// Reserve extra space for future updates (percentage)
    pub reserve_space_percent: u8,
    /// Verbose logging
    pub verbose: bool,
}

impl Default for HotReloadConfig {
    fn default() -> Self {
        Self {
            create_backup: true,
            verify_after_write: true,
            reserve_space_percent: 10,
            verbose: false,
        }
    }
}

/// Hot-reload manager for SMF files.
pub struct HotReloadManager {
    /// Configuration
    config: HotReloadConfig,
}

impl HotReloadManager {
    /// Create a new hot-reload manager.
    pub fn new(config: HotReloadConfig) -> Self {
        Self { config }
    }

    /// Update note.sdn section in an SMF file.
    ///
    /// This uses the zero-size trick: the section table entry shows size=0,
    /// so we can rewrite the section data without updating the section table.
    pub fn update_note_sdn(
        &self,
        smf_path: &Path,
        new_metadata: &NoteSdnMetadata,
    ) -> HotReloadResult {
        // Serialize new metadata
        let new_content = new_metadata.to_sdn();
        let new_size = new_content.len();

        if self.config.verbose {
            eprintln!("[hot-reload] Updating {:?} with {} bytes", smf_path, new_size);
        }

        // Find note.sdn section info
        let section_info = match self.find_note_sdn_section(smf_path) {
            Ok(info) => info,
            Err(e) => return HotReloadResult::InvalidSmf { message: e },
        };

        // Check if new data fits
        if new_size > section_info.available_space {
            return HotReloadResult::NeedRebuild {
                current_size: section_info.current_size,
                required_size: new_size,
                available_space: section_info.available_space,
            };
        }

        // Create backup if configured
        if self.config.create_backup {
            if let Err(e) = self.create_backup(smf_path) {
                return HotReloadResult::IoError {
                    message: format!("Failed to create backup: {}", e),
                };
            }
        }

        // Write new data
        if let Err(e) = self.write_note_sdn(smf_path, section_info.offset, &new_content) {
            return HotReloadResult::IoError {
                message: format!("Failed to write: {}", e),
            };
        }

        // Verify if configured
        if self.config.verify_after_write {
            if let Err(e) = self.verify_note_sdn(smf_path, section_info.offset, &new_content) {
                return HotReloadResult::IoError {
                    message: format!("Verification failed: {}", e),
                };
            }
        }

        HotReloadResult::Success
    }

    /// Add a new instantiation to an existing SMF file.
    pub fn add_instantiation(
        &self,
        smf_path: &Path,
        entry: InstantiationEntry,
    ) -> HotReloadResult {
        // Load existing metadata
        let mut metadata = match self.load_note_sdn(smf_path) {
            Ok(m) => m,
            Err(e) => return HotReloadResult::InvalidSmf { message: e },
        };

        // Add new entry
        metadata.add_instantiation(entry);

        // Update file
        self.update_note_sdn(smf_path, &metadata)
    }

    /// Move an entry from 'possible' to 'instantiations' after JIT compilation.
    pub fn mark_as_jit_compiled(
        &self,
        smf_path: &Path,
        mangled_name: &str,
    ) -> HotReloadResult {
        // Load existing metadata
        let mut metadata = match self.load_note_sdn(smf_path) {
            Ok(m) => m,
            Err(e) => return HotReloadResult::InvalidSmf { message: e },
        };

        // Find in possible
        let possible_entry = metadata.possible
            .iter()
            .find(|p| p.mangled_name == mangled_name)
            .cloned();

        if let Some(entry) = possible_entry {
            // Remove from possible
            metadata.possible.retain(|p| p.mangled_name != mangled_name);

            // Add to instantiations
            let inst_entry = InstantiationEntry::new(
                entry.template,
                vec![], // Type args already in mangled name
                entry.mangled_name,
                smf_path.to_string_lossy().to_string(),
                format!("{}:jit", smf_path.display()),
                "jit_memory".to_string(),
                InstantiationStatus::JitCompiled,
            );
            metadata.add_instantiation(inst_entry);

            // Update file
            self.update_note_sdn(smf_path, &metadata)
        } else {
            HotReloadResult::InvalidSmf {
                message: format!("Symbol {} not found in possible table", mangled_name),
            }
        }
    }

    /// Find note.sdn section information in SMF file.
    fn find_note_sdn_section(&self, smf_path: &Path) -> Result<NoteSdnSectionInfo, String> {
        let mut file = File::open(smf_path)
            .map_err(|e| format!("Failed to open file: {}", e))?;

        let file_size = file.metadata()
            .map_err(|e| format!("Failed to get file size: {}", e))?
            .len();

        // Read the entire file to find note.sdn section
        // TODO: Proper SMF header parsing to find section offset
        let mut content = String::new();
        file.read_to_string(&mut content)
            .map_err(|e| format!("Failed to read file: {}", e))?;

        // Find note.sdn section start
        let start_marker = "# Instantiation To/From Metadata";
        let offset = content.find(start_marker)
            .ok_or_else(|| "note.sdn section not found".to_string())? as u64;

        // Find current size (up to terminator)
        let section_content = &content[offset as usize..];
        let current_size = section_content.find(NOTE_SDN_TERMINATOR)
            .map(|pos| pos + NOTE_SDN_TERMINATOR.len())
            .unwrap_or(section_content.len());

        // Calculate available space (up to next section or EOF)
        // TODO: Proper calculation using section table
        let available_space = (file_size - offset) as usize;

        Ok(NoteSdnSectionInfo {
            offset,
            current_size,
            available_space,
        })
    }

    /// Load note.sdn metadata from SMF file.
    fn load_note_sdn(&self, smf_path: &Path) -> Result<NoteSdnMetadata, String> {
        let mut file = File::open(smf_path)
            .map_err(|e| format!("Failed to open file: {}", e))?;

        let mut content = String::new();
        file.read_to_string(&mut content)
            .map_err(|e| format!("Failed to read file: {}", e))?;

        // Find and extract note.sdn section
        let start_marker = "# Instantiation To/From Metadata";
        let start = content.find(start_marker)
            .ok_or_else(|| "note.sdn section not found".to_string())?;

        let section_content = &content[start..];
        let end = section_content.find(NOTE_SDN_TERMINATOR)
            .map(|pos| pos + NOTE_SDN_TERMINATOR.len())
            .unwrap_or(section_content.len());

        let sdn_content = &section_content[..end];

        // Parse SDN
        // TODO: Implement proper SDN parsing
        Ok(NoteSdnMetadata::new())
    }

    /// Write note.sdn content to SMF file.
    fn write_note_sdn(
        &self,
        smf_path: &Path,
        offset: u64,
        content: &str,
    ) -> Result<(), String> {
        let mut file = OpenOptions::new()
            .write(true)
            .open(smf_path)
            .map_err(|e| format!("Failed to open file for writing: {}", e))?;

        file.seek(SeekFrom::Start(offset))
            .map_err(|e| format!("Failed to seek: {}", e))?;

        file.write_all(content.as_bytes())
            .map_err(|e| format!("Failed to write: {}", e))?;

        file.flush()
            .map_err(|e| format!("Failed to flush: {}", e))?;

        Ok(())
    }

    /// Verify note.sdn content after write.
    fn verify_note_sdn(
        &self,
        smf_path: &Path,
        offset: u64,
        expected: &str,
    ) -> Result<(), String> {
        let mut file = File::open(smf_path)
            .map_err(|e| format!("Failed to open file: {}", e))?;

        file.seek(SeekFrom::Start(offset))
            .map_err(|e| format!("Failed to seek: {}", e))?;

        let mut actual = vec![0u8; expected.len()];
        file.read_exact(&mut actual)
            .map_err(|e| format!("Failed to read: {}", e))?;

        let actual_str = String::from_utf8_lossy(&actual);
        if actual_str != expected {
            return Err("Content mismatch after write".to_string());
        }

        Ok(())
    }

    /// Create backup of SMF file.
    fn create_backup(&self, smf_path: &Path) -> Result<(), String> {
        let backup_path = smf_path.with_extension("smf.bak");
        std::fs::copy(smf_path, &backup_path)
            .map_err(|e| format!("Failed to create backup: {}", e))?;

        if self.config.verbose {
            eprintln!("[hot-reload] Backup created: {:?}", backup_path);
        }

        Ok(())
    }
}

/// Information about note.sdn section in SMF file.
#[derive(Debug)]
struct NoteSdnSectionInfo {
    /// File offset where section data starts
    offset: u64,
    /// Current data size
    current_size: usize,
    /// Available space until next section
    available_space: usize,
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use tempfile::NamedTempFile;

    fn create_test_smf() -> NamedTempFile {
        let mut file = NamedTempFile::new().unwrap();
        let content = r#"# Some SMF header content

# Instantiation To/From Metadata
# Format version: 1.0

instantiations |id, template, type_args, mangled_name, from_file, from_loc, to_obj, status|

possible |id, template, type_args, mangled_name, required_by, can_defer|

type_inferences |id, inferred_type, expr, context, from_file, from_loc|

dependencies |from_inst, to_inst, dep_kind|

circular_warnings |id, cycle_path, severity|

circular_errors |id, cycle_path, error_code|

# END_NOTE

# More SMF content after note.sdn
"#;
        file.write_all(content.as_bytes()).unwrap();
        file.flush().unwrap();
        file
    }

    #[test]
    fn test_hot_reload_manager_basic() {
        let config = HotReloadConfig::default();
        let manager = HotReloadManager::new(config);

        assert!(manager.config.create_backup);
        assert!(manager.config.verify_after_write);
    }

    #[test]
    fn test_find_note_sdn_section() {
        let file = create_test_smf();
        let config = HotReloadConfig {
            verbose: false,
            ..Default::default()
        };
        let manager = HotReloadManager::new(config);

        let info = manager.find_note_sdn_section(file.path()).unwrap();
        assert!(info.offset > 0);
        assert!(info.current_size > 0);
        assert!(info.available_space >= info.current_size);
    }

    #[test]
    fn test_update_note_sdn() {
        let file = create_test_smf();
        let config = HotReloadConfig {
            create_backup: false, // Don't create backup in test
            verify_after_write: true,
            ..Default::default()
        };
        let manager = HotReloadManager::new(config);

        let metadata = NoteSdnMetadata::new();
        let result = manager.update_note_sdn(file.path(), &metadata);

        // Should succeed with empty metadata
        assert!(matches!(result, HotReloadResult::Success));
    }
}
