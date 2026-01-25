//! Unified database abstraction for SDN-backed databases
//!
//! This module provides a generic `Database<T>` implementation that consolidates
//! duplication across todo_db, feature_db, and task_db modules. It handles:
//! - Thread-safe locking during read/write operations
//! - Atomic writes to prevent file corruption
//! - Automatic serialization/deserialization via SDN format
//! - Consistent behavior across all database types

use crate::db_lock::FileLock;
use std::collections::BTreeMap;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

/// Trait for database records
///
/// Implement this trait to make a type usable with the generic Database<T>.
pub trait Record: Clone {
    /// Get the unique identifier for this record
    fn id(&self) -> String;

    /// Get the table name in the SDN database (e.g., "todos", "features", "tasks")
    fn table_name() -> &'static str;

    /// Get the field names for the table columns
    fn field_names() -> &'static [&'static str];

    /// Deserialize a record from an SDN table row
    fn from_sdn_row(row: &[String]) -> Result<Self, String>;

    /// Serialize a record to an SDN table row
    fn to_sdn_row(&self) -> Vec<String>;
}

/// Generic database for any Record type
///
/// Handles all IO, locking, and synchronization for SDN-backed databases.
///
/// # Examples
///
/// ```
/// use simple_driver::unified_db::{Database, Record};
///
/// #[derive(Clone, Debug)]
/// struct MyRecord {
///     id: String,
///     value: String,
/// }
///
/// impl Record for MyRecord {
///     fn id(&self) -> String {
///         self.id.clone()
///     }
///
///     fn table_name() -> &'static str {
///         "records"
///     }
///
///     fn field_names() -> &'static [&'static str] {
///         &["id", "value"]
///     }
///
///     fn from_sdn_row(row: &[String]) -> Result<Self, String> {
///         Ok(MyRecord {
///             id: row.get(0).cloned().unwrap_or_default(),
///             value: row.get(1).cloned().unwrap_or_default(),
///         })
///     }
///
///     fn to_sdn_row(&self) -> Vec<String> {
///         vec![self.id.clone(), self.value.clone()]
///     }
/// }
///
/// // Create a new database
/// let mut db: Database<MyRecord> = Database::new("/tmp/test_db.sdn");
///
/// // Insert a record
/// let record = MyRecord {
///     id: "1".to_string(),
///     value: "test".to_string(),
/// };
/// db.insert(record);
///
/// // Retrieve the record
/// assert!(db.get("1").is_some());
/// assert_eq!(db.get("1").unwrap().value, "test");
///
/// // Count records
/// assert_eq!(db.count(), 1);
/// ```
pub struct Database<T: Record> {
    /// In-memory records indexed by ID
    pub records: BTreeMap<String, T>,

    /// Path to the database file
    path: PathBuf,
}

impl<T: Record> Database<T> {
    /// Create a new empty database at the specified path
    pub fn new(path: impl AsRef<Path>) -> Self {
        Database {
            records: BTreeMap::new(),
            path: path.as_ref().to_path_buf(),
        }
    }

    /// Load database from disk with file locking
    ///
    /// # Arguments
    /// * `path` - Path to the .sdn database file
    ///
    /// # Returns
    /// * `Ok(Database)` - Database loaded successfully
    /// * `Err(String)` - Lock failure or parse error
    pub fn load(path: impl AsRef<Path>) -> Result<Self, String> {
        let path = path.as_ref();

        // Acquire lock
        let _lock = FileLock::acquire(path, 10).map_err(|e| format!("Failed to acquire lock: {:?}", e))?;

        // Create database instance
        let mut db = Database::new(path);

        // Read file if it exists
        if !path.exists() {
            return Ok(db);
        }

        let content = fs::read_to_string(path).map_err(|e| format!("Failed to read {}: {}", path.display(), e))?;

        // Parse SDN document
        let doc = simple_sdn::parse_document(&content).map_err(|e| format!("Failed to parse SDN: {}", e))?;

        // Extract root value
        let root = doc.root();

        // Get the table for this record type
        let table_data = match root {
            simple_sdn::SdnValue::Dict(dict) => dict.get(T::table_name()),
            simple_sdn::SdnValue::Table { .. } if T::table_name() == "todos" => Some(root),
            _ => None,
        };

        // Parse table rows
        if let Some(simple_sdn::SdnValue::Table {
            fields: Some(fields),
            rows,
            ..
        }) = table_data
        {
            for row in rows {
                let mut row_strings = Vec::new();
                for value in row {
                    row_strings.push(sdn_value_to_string(value));
                }

                // Skip empty rows
                if row_strings.is_empty() || row_strings[0].is_empty() {
                    continue;
                }

                // Deserialize record
                match T::from_sdn_row(&row_strings) {
                    Ok(record) => {
                        db.records.insert(record.id(), record);
                    }
                    Err(e) => {
                        eprintln!("Failed to deserialize record: {}", e);
                    }
                }
            }
        }

        Ok(db)
    }

    /// Save database to disk with atomic write and locking.
    /// Preserves other tables in the same file (multi-table support).
    pub fn save(&self) -> Result<(), io::Error> {
        // Acquire lock
        let _lock =
            FileLock::acquire(&self.path, 10).map_err(|e| io::Error::new(io::ErrorKind::Other, format!("{:?}", e)))?;

        // Load existing file to preserve other tables
        let mut existing_dict = indexmap::IndexMap::new();
        if self.path.exists() {
            if let Ok(content) = fs::read_to_string(&self.path) {
                if let Ok(doc) = simple_sdn::parse_document(&content) {
                    if let simple_sdn::SdnValue::Dict(dict) = doc.root() {
                        existing_dict = dict.clone();
                    }
                }
            }
        }

        // Build field list from Record trait
        let fields: Vec<String> = T::field_names().iter().map(|s| s.to_string()).collect();

        // Convert records to SDN rows
        let mut rows = Vec::new();
        for record in self.records.values() {
            let row: Vec<simple_sdn::SdnValue> = record
                .to_sdn_row()
                .into_iter()
                .map(|s| simple_sdn::SdnValue::String(s))
                .collect();
            rows.push(row);
        }

        // Create SDN table
        let table = simple_sdn::SdnValue::Table {
            fields: if fields.is_empty() { None } else { Some(fields) },
            types: None,
            rows,
        };

        // Update only this table in the existing dict (preserves other tables)
        existing_dict.insert(T::table_name().to_string(), table);

        // Create empty document for serialization
        let mut doc = simple_sdn::SdnDocument::parse("_placeholder: 1")
            .map_err(|e| io::Error::other(e.to_string()))?;
        *doc.root_mut() = simple_sdn::SdnValue::Dict(existing_dict);

        let content = doc.to_sdn();

        // Create parent directories
        if let Some(parent) = self.path.parent() {
            fs::create_dir_all(parent)?;
        }

        // Atomic write: write to temp, then rename
        let temp_path = self.path.with_extension("sdn.tmp");
        fs::write(&temp_path, content)?;
        fs::rename(&temp_path, &self.path)?;

        Ok(())
    }

    /// Get a record by ID (immutable)
    pub fn get(&self, id: &str) -> Option<&T> {
        self.records.get(id)
    }

    /// Get a record by ID (mutable)
    pub fn get_mut(&mut self, id: &str) -> Option<&mut T> {
        self.records.get_mut(id)
    }

    /// Insert a record into the database
    pub fn insert(&mut self, record: T) {
        self.records.insert(record.id(), record);
    }

    /// Delete a record by ID
    pub fn delete(&mut self, id: &str) -> Option<T> {
        self.records.remove(id)
    }

    /// Get all records
    pub fn all(&self) -> Vec<&T> {
        self.records.values().collect()
    }

    /// Get all records (mutable)
    pub fn all_mut(&mut self) -> Vec<&mut T> {
        self.records.values_mut().collect()
    }

    /// Get the count of records
    pub fn count(&self) -> usize {
        self.records.len()
    }

    /// Check if database is empty
    pub fn is_empty(&self) -> bool {
        self.records.is_empty()
    }
}

/// Helper function to convert SDN values to strings
fn sdn_value_to_string(value: &simple_sdn::SdnValue) -> String {
    match value {
        simple_sdn::SdnValue::String(s) => s.clone(),
        simple_sdn::SdnValue::Int(n) => n.to_string(),
        simple_sdn::SdnValue::Float(f) => f.to_string(),
        simple_sdn::SdnValue::Bool(b) => b.to_string(),
        simple_sdn::SdnValue::Null => String::new(),
        _ => format!("{:?}", value),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Debug)]
    struct TestRecord {
        id: String,
        name: String,
    }

    impl Record for TestRecord {
        fn id(&self) -> String {
            self.id.clone()
        }

        fn table_name() -> &'static str {
            "test_records"
        }

        fn field_names() -> &'static [&'static str] {
            &["id", "name"]
        }

        fn from_sdn_row(row: &[String]) -> Result<Self, String> {
            Ok(TestRecord {
                id: row.get(0).cloned().unwrap_or_default(),
                name: row.get(1).cloned().unwrap_or_default(),
            })
        }

        fn to_sdn_row(&self) -> Vec<String> {
            vec![self.id.clone(), self.name.clone()]
        }
    }

    #[test]
    fn test_database_create() {
        let db: Database<TestRecord> = Database::new("/tmp/test.sdn");
        assert_eq!(db.count(), 0);
    }

    #[test]
    fn test_database_insert() {
        let mut db: Database<TestRecord> = Database::new("/tmp/test.sdn");
        let record = TestRecord {
            id: "1".to_string(),
            name: "test".to_string(),
        };
        db.insert(record);
        assert_eq!(db.count(), 1);
    }

    #[test]
    fn test_database_get() {
        let mut db: Database<TestRecord> = Database::new("/tmp/test.sdn");
        let record = TestRecord {
            id: "1".to_string(),
            name: "test".to_string(),
        };
        db.insert(record.clone());
        assert!(db.get("1").is_some());
        assert_eq!(db.get("1").unwrap().name, "test");
    }

    #[test]
    fn test_database_delete() {
        let mut db: Database<TestRecord> = Database::new("/tmp/test.sdn");
        let record = TestRecord {
            id: "1".to_string(),
            name: "test".to_string(),
        };
        db.insert(record);
        assert_eq!(db.count(), 1);
        db.delete("1");
        assert_eq!(db.count(), 0);
    }
}
