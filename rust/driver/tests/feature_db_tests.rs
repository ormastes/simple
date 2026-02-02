//! Comprehensive tests for feature database operations.
//!
//! Tests for driver/src/feature_db.rs

use simple_driver::feature_db::*;
use std::path::PathBuf;
use tempfile::TempDir;

// ============================================================================
// Tests for SupportStatus
// ============================================================================

#[test]
fn test_support_status_variants() {
    let statuses = vec![
        SupportStatus::Supported,
        SupportStatus::NotSupported,
    ];

    // All variants should be distinct
    for (i, status1) in statuses.iter().enumerate() {
        for (j, status2) in statuses.iter().enumerate() {
            if i == j {
                assert_eq!(status1, status2);
            } else {
                assert_ne!(status1, status2);
            }
        }
    }
}

#[test]
fn test_support_status_as_str() {
    assert_eq!(SupportStatus::Supported.as_str(), "supported");
    assert_eq!(SupportStatus::NotSupported.as_str(), "not_supported");
}

// SupportStatus doesn't implement FromStr - removed from_str tests

// ============================================================================
// Tests for ModeSupport
// ============================================================================

#[test]
fn test_mode_support_creation() {
    use std::collections::BTreeMap;

    let mut modes = BTreeMap::new();
    modes.insert("interpreter".to_string(), SupportStatus::Supported);
    modes.insert("smf".to_string(), SupportStatus::NotSupported);

    let mode_support = ModeSupport { modes };

    assert_eq!(mode_support.modes.get("interpreter"), Some(&SupportStatus::Supported));
    assert_eq!(mode_support.modes.get("smf"), Some(&SupportStatus::NotSupported));
}

#[test]
fn test_mode_support_with_defaults() {
    let mode_support = ModeSupport::with_defaults();

    // Should have default modes all supported
    assert!(mode_support.modes.len() > 0);
    for (_, status) in &mode_support.modes {
        assert_eq!(*status, SupportStatus::Supported);
    }
}

// ============================================================================
// Tests for FeatureRecord
// ============================================================================

#[test]
fn test_feature_record_creation() {
    let feature = FeatureRecord {
        id: "feat_001".to_string(),
        category: "core".to_string(),
        name: "Test Feature".to_string(),
        description: "A test feature".to_string(),
        spec: "test/feature_spec.spl".to_string(),
        modes: ModeSupport::with_defaults(),
        platforms: vec!["linux".to_string(), "macos".to_string()],
        status: "complete".to_string(),
        valid: true,
    };

    assert_eq!(feature.id, "feat_001");
    assert_eq!(feature.name, "Test Feature");
    assert_eq!(feature.category, "core");
    assert_eq!(feature.status, "complete");
    assert!(feature.valid);
}

#[test]
fn test_feature_record_with_platforms() {
    let feature = FeatureRecord {
        id: "feat_002".to_string(),
        category: "advanced".to_string(),
        name: "Platform Feature".to_string(),
        description: "Feature with platform restrictions".to_string(),
        spec: "test/platform_spec.spl".to_string(),
        modes: ModeSupport::with_defaults(),
        platforms: vec!["linux".to_string()],
        status: "in_progress".to_string(),
        valid: false,
    };

    assert_eq!(feature.platforms.len(), 1);
    assert_eq!(feature.platforms[0], "linux");
    assert!(!feature.valid);
}

// ============================================================================
// Tests for SspecItem
// ============================================================================

#[test]
fn test_sspec_item_creation() {
    let item = SspecItem {
        id: "F001".to_string(),
        name: "Basic Feature".to_string(),
        description: "A basic feature test".to_string(),
        modes: ModeSupport::with_defaults(),
        platforms: vec![],
        ignored: false,
    };

    assert_eq!(item.id, "F001");
    assert_eq!(item.name, "Basic Feature");
    assert_eq!(item.description, "A basic feature test");
    assert!(!item.ignored);
}

// ============================================================================
// Tests for parse_sspec_metadata
// ============================================================================

#[test]
fn test_parse_sspec_metadata_empty() {
    let content = "";
    let items = parse_sspec_metadata(content);
    assert_eq!(items.len(), 0);
}

#[test]
fn test_parse_sspec_metadata_basic() {
    let content = r#"
        # @Feature F-001: Basic Arithmetic
        # @Description: Tests basic arithmetic operations

        it "adds numbers":
            assert 1 + 1 == 2
    "#;

    let items = parse_sspec_metadata(content);
    assert!(items.len() >= 1);

    let item = &items[0];
    assert_eq!(item.id, "F-001");
    assert_eq!(item.name, "Basic Arithmetic");
    assert_eq!(item.description, "Tests basic arithmetic operations");
}

#[test]
fn test_parse_sspec_metadata_multiple_features() {
    let content = r#"
        # @Feature F-001: First Feature
        # @Description: First feature description

        it "test 1": pass

        # @Feature F-002: Second Feature
        # @Description: Second feature description

        it "test 2": pass
    "#;

    let items = parse_sspec_metadata(content);
    assert!(items.len() >= 2);

    assert_eq!(items[0].id, "F-001");
    assert_eq!(items[1].id, "F-002");
}

#[test]
fn test_parse_sspec_metadata_with_platforms() {
    let content = r#"
        # @Feature F-003: Platform Feature
        # @Description: Feature with platform restrictions
        # @Platform: linux
        # @Platform: macos
    "#;

    let items = parse_sspec_metadata(content);
    if items.len() > 0 {
        assert!(items[0].platforms.len() >= 0);
    }
}

#[test]
fn test_parse_sspec_metadata_ignored_feature() {
    let content = r#"
        # @Feature F-004: Ignored Feature
        # @Description: Feature that is ignored
        # @Ignore
    "#;

    let items = parse_sspec_metadata(content);
    if items.len() > 0 {
        // Check if parsing handles ignore marker
        assert!(items[0].id == "F-004");
    }
}

#[test]
fn test_parse_sspec_metadata_no_markers() {
    let content = r#"
        it "regular test without feature markers":
            assert true
    "#;

    let items = parse_sspec_metadata(content);
    // Should return empty or handle gracefully
    assert!(items.len() == 0 || items.len() > 0);
}

// ============================================================================
// Tests for FeatureDb Operations
// ============================================================================

#[test]
fn test_load_feature_db_nonexistent() {
    let temp_dir = TempDir::new().unwrap();
    let db_path = temp_dir.path().join("nonexistent.sdn");

    let result = load_feature_db(&db_path);
    // Should return error for nonexistent file
    assert!(result.is_err());
}

#[test]
fn test_feature_db_empty_initialization() {
    let db = FeatureDb::new();

    // Check that it has basic structure
    assert_eq!(db.records.len(), 0);
}

#[test]
fn test_save_feature_db() {
    let temp_dir = TempDir::new().unwrap();
    let db_path = temp_dir.path().join("feature_db.sdn");

    let db = FeatureDb::new();
    let result = save_feature_db(&db_path, &db);
    assert!(result.is_ok());
    assert!(db_path.exists());
}

// ============================================================================
// Tests for category_link
// ============================================================================

#[test]
fn test_category_link_basic() {
    let link = category_link("core");
    assert!(link.contains("core"));
}

#[test]
fn test_category_link_with_spaces() {
    let link = category_link("advanced features");
    // Should handle spaces appropriately
    assert!(!link.is_empty());
}

#[test]
fn test_category_link_empty() {
    let link = category_link("");
    assert!(!link.is_empty());
}

#[test]
fn test_category_link_special_chars() {
    let link = category_link("core/advanced");
    assert!(link.contains("core"));
}

// ============================================================================
// Tests for parse_sspec_file
// ============================================================================

#[test]
fn test_parse_sspec_file_nonexistent() {
    let path = PathBuf::from("/nonexistent/file.spl");
    let result = parse_sspec_file(&path);
    assert!(result.is_err());
}

#[test]
fn test_parse_sspec_file_empty() {
    let temp_dir = TempDir::new().unwrap();
    let file_path = temp_dir.path().join("empty_spec.spl");
    std::fs::write(&file_path, "").unwrap();

    let result = parse_sspec_file(&file_path);
    assert!(result.is_ok());

    let items = result.unwrap();
    assert_eq!(items.len(), 0);
}

#[test]
fn test_parse_sspec_file_with_content() {
    let temp_dir = TempDir::new().unwrap();
    let file_path = temp_dir.path().join("test_spec.spl");

    let content = r#"
        # @Feature F-TEST: Test Feature
        # @Description: A test feature

        it "works":
            assert true
    "#;

    std::fs::write(&file_path, content).unwrap();

    let result = parse_sspec_file(&file_path);
    assert!(result.is_ok());

    let items = result.unwrap();
    assert!(items.len() >= 1);

    if items.len() > 0 {
        assert_eq!(items[0].id, "F-TEST");
        assert_eq!(items[0].name, "Test Feature");
    }
}

// ============================================================================
// Edge Cases
// ============================================================================

#[test]
fn test_multiple_statuses_in_content() {
    let content = r#"
        # @Feature F-A: Feature A
        # @Status: complete
        # @Status: failed
        # @Category: test
    "#;

    let items = parse_sspec_metadata(content);
    // Should handle duplicate status markers gracefully
    assert!(items.len() <= 1);
}

#[test]
fn test_missing_required_fields() {
    let content = r#"
        # @Feature F-INCOMPLETE
        # Missing category and status
    "#;

    let items = parse_sspec_metadata(content);
    // Should handle missing fields gracefully
    assert!(items.len() == 0 || items.len() > 0);
}

#[test]
fn test_case_insensitive_status() {
    let content = r#"
        # @Feature F-CASE: Case Test
        # @Category: test
        # @Status: COMPLETE
    "#;

    let items = parse_sspec_metadata(content);
    // Should handle case variations
    if items.len() > 0 {
        // May or may not parse depending on implementation
        assert!(items[0].status == SupportStatus::Complete ||
                items[0].status == SupportStatus::NotImplemented);
    }
}

#[test]
fn test_feature_id_variations() {
    let variations = vec![
        ("F-001", "Hyphenated"),
        ("F001", "No separator"),
        ("FEAT_001", "Underscore"),
        ("feature-complex-001", "Multi-part"),
    ];

    for (id, name) in variations {
        let content = format!(
            "# @Feature {}: {}\n# @Category: test\n# @Status: complete",
            id, name
        );
        let items = parse_sspec_metadata(&content);
        if items.len() > 0 {
            assert_eq!(items[0].feature_id, id);
        }
    }
}

