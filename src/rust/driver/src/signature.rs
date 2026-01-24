//! Signature module for qualified ignore authentication.
//!
//! Computes and verifies SHA256 signatures over qualified_ignore records
//! to detect tampering. Only qualified_ignore fields are signed - normal
//! test results (pass/fail/timing) update without re-authentication.

use crate::test_db::{TestDb, TestRecord, TestStatus};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;

/// Signature for qualified ignore records
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QualifiedIgnoreSignature {
    /// SHA256 hash of all qualified_ignore records (hex string)
    pub hash: String,
    /// Who signed this (email or "password:<hash-prefix>")
    pub signer: String,
    /// When the signature was created (ISO timestamp)
    pub signed_at: String,
    /// Number of qualified_ignore records covered
    pub record_count: usize,
}

/// Compute the hash of all qualified_ignore records in the database.
///
/// Only the qualified_ignore-specific fields are hashed:
/// - test_id
/// - qualified_by
/// - qualified_at
/// - qualified_reason
///
/// This allows normal test results to update without invalidating the signature.
pub fn compute_qualified_ignore_hash(db: &TestDb) -> String {
    let mut hasher = Sha256::new();

    // Get qualified_ignore records sorted by test_id for deterministic ordering
    let mut qualified_records: BTreeMap<&str, &TestRecord> = BTreeMap::new();
    for (id, record) in &db.records {
        if record.status == TestStatus::QualifiedIgnore {
            qualified_records.insert(id.as_str(), record);
        }
    }

    // Hash each record's qualified_ignore fields
    for (test_id, record) in qualified_records {
        hasher.update(test_id.as_bytes());
        hasher.update(b"\x00"); // null separator

        if let Some(ref qualified_by) = record.qualified_by {
            hasher.update(qualified_by.as_bytes());
        }
        hasher.update(b"\x00");

        if let Some(ref qualified_at) = record.qualified_at {
            hasher.update(qualified_at.as_bytes());
        }
        hasher.update(b"\x00");

        if let Some(ref qualified_reason) = record.qualified_reason {
            hasher.update(qualified_reason.as_bytes());
        }
        hasher.update(b"\x00\x00"); // double null as record separator
    }

    // Return hex-encoded hash
    format!("{:x}", hasher.finalize())
}

/// Sign the qualified_ignore records in the database
pub fn sign_qualified_ignores(db: &TestDb, signer: &str) -> QualifiedIgnoreSignature {
    let hash = compute_qualified_ignore_hash(db);
    let record_count = db
        .records
        .values()
        .filter(|r| r.status == TestStatus::QualifiedIgnore)
        .count();

    QualifiedIgnoreSignature {
        hash,
        signer: signer.to_string(),
        signed_at: chrono::Utc::now().to_rfc3339(),
        record_count,
    }
}

/// Verify a signature against the current database state
pub fn verify_signature(db: &TestDb, sig: &QualifiedIgnoreSignature) -> SignatureVerifyResult {
    let current_hash = compute_qualified_ignore_hash(db);
    let current_count = db
        .records
        .values()
        .filter(|r| r.status == TestStatus::QualifiedIgnore)
        .count();

    if current_hash == sig.hash {
        SignatureVerifyResult::Valid
    } else if current_count != sig.record_count {
        SignatureVerifyResult::RecordCountMismatch {
            expected: sig.record_count,
            actual: current_count,
        }
    } else {
        SignatureVerifyResult::HashMismatch {
            expected: sig.hash.clone(),
            actual: current_hash,
        }
    }
}

/// Result of signature verification
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SignatureVerifyResult {
    /// Signature is valid
    Valid,
    /// Hash doesn't match - records were modified
    HashMismatch { expected: String, actual: String },
    /// Record count changed
    RecordCountMismatch { expected: usize, actual: usize },
}

impl SignatureVerifyResult {
    pub fn is_valid(&self) -> bool {
        matches!(self, SignatureVerifyResult::Valid)
    }
}

impl std::fmt::Display for SignatureVerifyResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SignatureVerifyResult::Valid => write!(f, "Signature valid"),
            SignatureVerifyResult::HashMismatch { expected, actual } => {
                write!(
                    f,
                    "Hash mismatch: expected {}, got {}",
                    &expected[..8.min(expected.len())],
                    &actual[..8.min(actual.len())]
                )
            }
            SignatureVerifyResult::RecordCountMismatch { expected, actual } => {
                write!(f, "Record count mismatch: expected {}, got {}", expected, actual)
            }
        }
    }
}

/// Load signature from test database SDN file
pub fn load_signature_from_db(db_path: &std::path::Path) -> Result<Option<QualifiedIgnoreSignature>, String> {
    let sig_path = db_path.with_extension("sig.sdn");

    if !sig_path.exists() {
        return Ok(None);
    }

    let content = std::fs::read_to_string(&sig_path)
        .map_err(|e| format!("Failed to read signature file: {}", e))?;

    if content.trim().is_empty() {
        return Ok(None);
    }

    // Parse signature from SDN
    match simple_sdn::parse_document(&content) {
        Ok(doc) => {
            let root = doc.root();
            if let simple_sdn::SdnValue::Dict(dict) = root {
                let hash = dict
                    .get("hash")
                    .and_then(|v| if let simple_sdn::SdnValue::String(s) = v { Some(s.clone()) } else { None })
                    .unwrap_or_default();
                let signer = dict
                    .get("signer")
                    .and_then(|v| if let simple_sdn::SdnValue::String(s) = v { Some(s.clone()) } else { None })
                    .unwrap_or_default();
                let signed_at = dict
                    .get("signed_at")
                    .and_then(|v| if let simple_sdn::SdnValue::String(s) = v { Some(s.clone()) } else { None })
                    .unwrap_or_default();
                let record_count = dict
                    .get("record_count")
                    .and_then(|v| if let simple_sdn::SdnValue::Int(n) = v { Some(*n as usize) } else { None })
                    .unwrap_or(0);

                if hash.is_empty() {
                    return Ok(None);
                }

                Ok(Some(QualifiedIgnoreSignature {
                    hash,
                    signer,
                    signed_at,
                    record_count,
                }))
            } else {
                Ok(None)
            }
        }
        Err(e) => Err(format!("Failed to parse signature file: {}", e)),
    }
}

/// Save signature to test database SDN file
pub fn save_signature_to_db(
    db_path: &std::path::Path,
    sig: &QualifiedIgnoreSignature,
) -> Result<(), String> {
    let sig_path = db_path.with_extension("sig.sdn");

    let content = format!(
        "# Qualified Ignore Signature\n\
         # DO NOT MODIFY - cryptographic signature for qualified_ignore records\n\n\
         hash: \"{}\"\n\
         signer: \"{}\"\n\
         signed_at: \"{}\"\n\
         record_count: {}\n",
        sig.hash, sig.signer, sig.signed_at, sig.record_count
    );

    // Atomic write
    let temp_path = sig_path.with_extension("sig.sdn.tmp");
    std::fs::write(&temp_path, &content)
        .map_err(|e| format!("Failed to write signature file: {}", e))?;
    std::fs::rename(&temp_path, &sig_path)
        .map_err(|e| format!("Failed to finalize signature file: {}", e))?;

    Ok(())
}

/// Check if the database has any qualified_ignore records
pub fn has_qualified_ignores(db: &TestDb) -> bool {
    db.records
        .values()
        .any(|r| r.status == TestStatus::QualifiedIgnore)
}

/// Get all test IDs with qualified_ignore status
pub fn get_qualified_ignore_ids(db: &TestDb) -> Vec<String> {
    db.records
        .iter()
        .filter(|(_, r)| r.status == TestStatus::QualifiedIgnore)
        .map(|(id, _)| id.clone())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_db::TestDb;

    #[test]
    fn test_empty_db_hash() {
        let db = TestDb::new();
        let hash = compute_qualified_ignore_hash(&db);
        // Empty DB should have a consistent hash
        assert!(!hash.is_empty());
        assert_eq!(hash.len(), 64); // SHA256 hex = 64 chars
    }

    #[test]
    fn test_sign_and_verify() {
        let db = TestDb::new();
        let sig = sign_qualified_ignores(&db, "test@example.com");

        assert_eq!(sig.signer, "test@example.com");
        assert_eq!(sig.record_count, 0);

        let result = verify_signature(&db, &sig);
        assert!(result.is_valid());
    }

    #[test]
    fn test_signature_verify_result_display() {
        assert_eq!(format!("{}", SignatureVerifyResult::Valid), "Signature valid");

        let mismatch = SignatureVerifyResult::HashMismatch {
            expected: "abcd1234".to_string(),
            actual: "efgh5678".to_string(),
        };
        assert!(format!("{}", mismatch).contains("mismatch"));
    }
}
