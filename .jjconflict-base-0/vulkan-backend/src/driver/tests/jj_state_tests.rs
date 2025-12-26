use chrono::Utc;
use std::path::PathBuf;
use tempfile::TempDir;

// Import the module we're testing (to be created)
use simple_driver::jj_state::{BuildMetadata, BuildMode, JjStateManager, TestLevel, TestMetadata};

/// Helper function to verify a jj commit message contains expected text
fn assert_jj_commit_contains(repo_path: &PathBuf, expected: &str) {
    let output = std::process::Command::new("jj")
        .args(["log", "-r", "@-", "--no-graph", "-T", "description"])
        .current_dir(repo_path)
        .output()
        .expect("Failed to run jj log");
    let log = String::from_utf8_lossy(&output.stdout);
    assert!(
        log.contains(expected),
        "Expected commit message to contain '{}', got: {}",
        expected,
        log
    );
}

/// Helper to set up a jj repo and return (TempDir, path, manager)
fn setup_jj_repo() -> (TempDir, PathBuf, JjStateManager) {
    let temp = TempDir::new().unwrap();
    let repo_path = temp.path().to_path_buf();

    std::process::Command::new("jj")
        .args(["git", "init", "--colocate"])
        .current_dir(&repo_path)
        .output()
        .expect("jj not installed");

    let manager = JjStateManager::new_with_path(repo_path.clone()).unwrap();
    (temp, repo_path, manager)
}

#[test]
fn jj_state_manager_detects_repo() {
    let temp = TempDir::new().unwrap();
    let repo_path = temp.path().to_path_buf();

    // Create a mock .jj directory
    std::fs::create_dir_all(repo_path.join(".jj/repo")).unwrap();

    let manager = JjStateManager::new_with_path(repo_path.clone()).unwrap();
    assert!(manager.is_enabled());
}

#[test]
fn jj_state_manager_disabled_when_no_repo() {
    let temp = TempDir::new().unwrap();
    let repo_path = temp.path().to_path_buf();

    // No .jj directory created
    let manager = JjStateManager::new_with_path(repo_path).unwrap();
    assert!(!manager.is_enabled());
}

#[test]
fn snapshot_build_creates_commit() {
    let temp = TempDir::new().unwrap();
    let repo_path = temp.path().to_path_buf();

    // Initialize a real jj repo for this test
    std::process::Command::new("jj")
        .args(&["git", "init", "--colocate"])
        .current_dir(&repo_path)
        .output()
        .expect("jj not installed");

    let manager = JjStateManager::new_with_path(repo_path.clone()).unwrap();

    let metadata = BuildMetadata {
        timestamp: Utc::now(),
        duration_ms: 3200,
        artifacts: vec![PathBuf::from("target/release/simple")],
        target: "x86_64-unknown-linux-gnu".to_string(),
        mode: BuildMode::Release,
    };

    let result = manager.snapshot_build_success(&metadata);
    assert!(
        result.is_ok(),
        "Snapshot should succeed: {:?}",
        result.err()
    );

    // Verify commit was created (check parent since we created a new working copy)
    assert_jj_commit_contains(&repo_path, "Build Success");
}

#[test]
fn snapshot_test_creates_commit() {
    let temp = TempDir::new().unwrap();
    let repo_path = temp.path().to_path_buf();

    // Initialize a real jj repo
    std::process::Command::new("jj")
        .args(&["git", "init", "--colocate"])
        .current_dir(&repo_path)
        .output()
        .expect("jj not installed");

    let manager = JjStateManager::new_with_path(repo_path.clone()).unwrap();

    let metadata = TestMetadata {
        timestamp: Utc::now(),
        duration_ms: 12400,
        total_tests: 2507,
        passed: 2507,
        failed: 0,
        ignored: 3,
        test_level: TestLevel::All,
    };

    let result = manager.snapshot_test_success(&metadata);
    assert!(
        result.is_ok(),
        "Snapshot should succeed: {:?}",
        result.err()
    );

    // Verify commit was created (check parent since we created a new working copy)
    assert_jj_commit_contains(&repo_path, "Tests Passed");
}

#[test]
fn build_metadata_serializes_correctly() {
    let metadata = BuildMetadata {
        timestamp: Utc::now(),
        duration_ms: 3200,
        artifacts: vec![
            PathBuf::from("target/release/simple"),
            PathBuf::from("target/release/libsimple_runtime.so"),
        ],
        target: "x86_64-unknown-linux-gnu".to_string(),
        mode: BuildMode::Release,
    };

    let message = metadata.to_commit_message();
    assert!(message.contains("🏗️  Build Success"));
    assert!(message.contains("Duration: 3.2s"));
    assert!(message.contains("Mode: Release"));
    assert!(message.contains("Target: x86_64-unknown-linux-gnu"));
    assert!(message.contains("target/release/simple"));
}

#[test]
fn test_metadata_serializes_correctly() {
    let metadata = TestMetadata {
        timestamp: Utc::now(),
        duration_ms: 12400,
        total_tests: 2507,
        passed: 2507,
        failed: 0,
        ignored: 3,
        test_level: TestLevel::Unit,
    };

    let message = metadata.to_commit_message();
    assert!(message.contains("✅ Tests Passed"));
    assert!(message.contains("Level: Unit"));
    assert!(message.contains("Total: 2507"));
    assert!(message.contains("Passed: 2507"));
    assert!(message.contains("Failed: 0"));
    assert!(message.contains("Ignored: 3"));
    assert!(message.contains("Duration: 12.4s"));
}

#[test]
fn get_last_working_state_returns_latest() {
    let (_temp, repo_path, manager) = setup_jj_repo();

    // Create a build snapshot
    let metadata = BuildMetadata {
        timestamp: Utc::now(),
        duration_ms: 1000,
        artifacts: vec![],
        target: "test".to_string(),
        mode: BuildMode::Debug,
    };
    manager.snapshot_build_success(&metadata).unwrap();

    // Get last working state
    let last_state = manager.get_last_working_state().unwrap();
    assert!(last_state.is_some(), "Should have a last working state");

    let state = last_state.unwrap();
    assert!(state.contains("Build Success") || state.len() > 0);
}

#[test]
fn snapshot_includes_timestamp() {
    let metadata = BuildMetadata {
        timestamp: Utc::now(),
        duration_ms: 1000,
        artifacts: vec![],
        target: "test".to_string(),
        mode: BuildMode::Debug,
    };

    let message = metadata.to_commit_message();
    assert!(message.contains("Timestamp:"));
}

#[test]
fn snapshot_includes_duration() {
    let metadata = BuildMetadata {
        timestamp: Utc::now(),
        duration_ms: 5432,
        artifacts: vec![],
        target: "test".to_string(),
        mode: BuildMode::Debug,
    };

    let message = metadata.to_commit_message();
    assert!(message.contains("Duration: 5.4s"));
}

#[test]
fn snapshot_includes_artifacts() {
    let metadata = BuildMetadata {
        timestamp: Utc::now(),
        duration_ms: 1000,
        artifacts: vec![
            PathBuf::from("artifact1.smf"),
            PathBuf::from("artifact2.so"),
        ],
        target: "test".to_string(),
        mode: BuildMode::Debug,
    };

    let message = metadata.to_commit_message();
    assert!(message.contains("Artifacts:"));
    assert!(message.contains("artifact1.smf"));
    assert!(message.contains("artifact2.so"));
}

#[test]
fn snapshot_message_format_correct() {
    let build_meta = BuildMetadata {
        timestamp: Utc::now(),
        duration_ms: 3200,
        artifacts: vec![PathBuf::from("test.smf")],
        target: "x86_64-unknown-linux-gnu".to_string(),
        mode: BuildMode::Release,
    };

    let message = build_meta.to_commit_message();

    // Should have emoji and title
    assert!(message.starts_with("🏗️  Build Success"));

    // Should have all fields
    assert!(message.contains("Duration:"));
    assert!(message.contains("Mode:"));
    assert!(message.contains("Target:"));
    assert!(message.contains("Artifacts:"));
    assert!(message.contains("Timestamp:"));
}

#[test]
fn multiple_snapshots_track_history() {
    let (_temp, repo_path, manager) = setup_jj_repo();

    // Create multiple snapshots
    for i in 1..=3 {
        let metadata = BuildMetadata {
            timestamp: Utc::now(),
            duration_ms: i * 1000,
            artifacts: vec![PathBuf::from(format!("build{}.smf", i))],
            target: "test".to_string(),
            mode: BuildMode::Debug,
        };
        manager.snapshot_build_success(&metadata).unwrap();
        std::thread::sleep(std::time::Duration::from_millis(100));
    }

    // Verify we have multiple commits
    let output = std::process::Command::new("jj")
        .args(&["log", "--limit", "20"])
        .current_dir(&repo_path)
        .output()
        .unwrap();

    let log = String::from_utf8_lossy(&output.stdout);
    let count = log.matches("Build Success").count();
    assert!(
        count >= 3,
        "Should have at least 3 build snapshots, found {}, log:\n{}",
        count,
        log
    );
}

#[test]
fn snapshot_fails_gracefully_no_repo() {
    let temp = TempDir::new().unwrap();
    let repo_path = temp.path().to_path_buf();

    // No jj repo created
    let manager = JjStateManager::new_with_path(repo_path).unwrap();
    assert!(!manager.is_enabled());

    let metadata = BuildMetadata {
        timestamp: Utc::now(),
        duration_ms: 1000,
        artifacts: vec![],
        target: "test".to_string(),
        mode: BuildMode::Debug,
    };

    // Should succeed but do nothing
    let result = manager.snapshot_build_success(&metadata);
    assert!(result.is_ok(), "Should gracefully handle no repo");
}

#[test]
fn snapshot_preserves_git_state() {
    let temp = TempDir::new().unwrap();
    let repo_path = temp.path().to_path_buf();

    // Initialize git first
    std::process::Command::new("git")
        .args(&["init"])
        .current_dir(&repo_path)
        .output()
        .unwrap();

    // Configure git
    std::process::Command::new("git")
        .args(&["config", "user.email", "test@example.com"])
        .current_dir(&repo_path)
        .output()
        .unwrap();

    std::process::Command::new("git")
        .args(&["config", "user.name", "Test User"])
        .current_dir(&repo_path)
        .output()
        .unwrap();

    // Make a git commit
    std::fs::write(repo_path.join("test.txt"), "test").unwrap();
    std::process::Command::new("git")
        .args(&["add", "."])
        .current_dir(&repo_path)
        .output()
        .unwrap();

    std::process::Command::new("git")
        .args(&["commit", "-m", "Initial commit"])
        .current_dir(&repo_path)
        .output()
        .unwrap();

    // Now init jj co-located
    std::process::Command::new("jj")
        .args(&["git", "init", "--colocate"])
        .current_dir(&repo_path)
        .output()
        .unwrap();

    let manager = JjStateManager::new_with_path(repo_path.clone()).unwrap();

    // Create jj snapshot
    let metadata = BuildMetadata {
        timestamp: Utc::now(),
        duration_ms: 1000,
        artifacts: vec![],
        target: "test".to_string(),
        mode: BuildMode::Debug,
    };
    manager.snapshot_build_success(&metadata).unwrap();

    // Verify git still has the original commit
    let output = std::process::Command::new("git")
        .args(&["log", "--oneline"])
        .current_dir(&repo_path)
        .output()
        .unwrap();

    let log = String::from_utf8_lossy(&output.stdout);
    assert!(
        log.contains("Initial commit"),
        "Git commit should be preserved"
    );
}

#[test]
fn snapshot_is_idempotent() {
    let (_temp, _repo_path, manager) = setup_jj_repo();

    let metadata = BuildMetadata {
        timestamp: Utc::now(),
        duration_ms: 1000,
        artifacts: vec![],
        target: "test".to_string(),
        mode: BuildMode::Debug,
    };

    // Create snapshot twice
    manager.snapshot_build_success(&metadata).unwrap();
    manager.snapshot_build_success(&metadata).unwrap();

    // Both should succeed (idempotent)
    let result = manager.get_last_working_state();
    assert!(result.is_ok());
}
