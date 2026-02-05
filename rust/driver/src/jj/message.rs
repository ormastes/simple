use super::event::BuildState;

/// Format build state messages for display
pub struct MessageFormatter;

impl MessageFormatter {
    /// Format a success message
    pub fn success(state: &BuildState) -> String {
        let mut lines = vec!["🎉 Build successful!".to_string()];

        if let (Some(passed), Some(total)) = (state.tests_passed, state.total_tests) {
            if passed == total {
                lines.push(format!("   ✓ All {} tests passed", total));
            }
        }

        if let Some(commit_id) = &state.commit_id {
            lines.push(format!("   Commit: {}", Self::short_commit(commit_id)));
        }

        lines.join("\n")
    }

    /// Format a failure message
    pub fn failure(state: &BuildState) -> String {
        let mut lines = vec!["❌ Build failed".to_string()];

        if !state.compilation_success {
            lines.push("   ✗ Compilation failed".to_string());
        }

        if let (Some(failed), Some(total)) = (state.tests_failed, state.total_tests) {
            if failed > 0 {
                lines.push(format!("   ✗ {}/{} tests failed", failed, total));
            }
        }

        if let Some(commit_id) = &state.commit_id {
            lines.push(format!("   Commit: {}", Self::short_commit(commit_id)));
        }

        lines.join("\n")
    }

    /// Format a progress message
    pub fn progress(message: &str) -> String {
        format!("⏳ {}", message)
    }

    /// Format an info message
    pub fn info(message: &str) -> String {
        format!("ℹ️  {}", message)
    }

    /// Truncate commit ID to short form
    fn short_commit(commit_id: &str) -> &str {
        if commit_id.len() > 12 {
            &commit_id[..12]
        } else {
            commit_id
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_success_message() {
        let state = BuildState::new()
            .with_commit("abcdef123456789".to_string())
            .mark_compilation_success()
            .set_test_results(10, 0, 10);

        let msg = MessageFormatter::success(&state);
        assert!(msg.contains("🎉 Build successful!"));
        assert!(msg.contains("✓ All 10 tests passed"));
        assert!(msg.contains("abcdef123456"));
        assert!(!msg.contains("789")); // Truncated
    }

    #[test]
    fn test_failure_message() {
        let state = BuildState::new()
            .with_commit("xyz789".to_string())
            .set_test_results(8, 2, 10);

        let msg = MessageFormatter::failure(&state);
        assert!(msg.contains("❌ Build failed"));
        assert!(msg.contains("✗ Compilation failed"));
        assert!(msg.contains("✗ 2/10 tests failed"));
        assert!(msg.contains("xyz789"));
    }

    #[test]
    fn test_progress_message() {
        let msg = MessageFormatter::progress("Running tests...");
        assert_eq!(msg, "⏳ Running tests...");
    }

    #[test]
    fn test_info_message() {
        let msg = MessageFormatter::info("Found 5 test files");
        assert_eq!(msg, "ℹ️  Found 5 test files");
    }

    #[test]
    fn test_short_commit_truncation() {
        assert_eq!(
            MessageFormatter::short_commit("abcdefghijklmnopqrstuvwxyz"),
            "abcdefghijkl"
        );
        assert_eq!(MessageFormatter::short_commit("short"), "short");
    }
}
