//! Build-script selected input guard. No compiler or source-selection policy here.
use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};

#[derive(Debug)]
pub struct RejectedInput {
    pub path: PathBuf,
    pub reason: String,
}

#[derive(Debug)]
pub struct SelectedInputError {
    pub target: String,
    pub root: PathBuf,
    pub rejected: Vec<RejectedInput>,
}

impl fmt::Display for SelectedInputError {
    fn fmt(&self, out: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(out, "runtime-selected-c-inputs-invalid target={:?} root={:?} count={}",
                 self.target, self.root, self.rejected.len())?;
        for input in &self.rejected {
            writeln!(out, "runtime-selected-c-input-rejected path={:?} reason={:?}",
                     input.path, input.reason)?;
        }
        Ok(())
    }
}

/// Validate every producer-selected C input before constructing the compiler job.
/// Existing target/feature selection remains in build.rs. Symlinks resolving to
/// files retain the existing compiler behavior; this is not a confinement API.
pub fn require_selected_c_inputs(
    root: &Path, selected: &[&str], target: &str,
) -> Result<Vec<PathBuf>, SelectedInputError> {
    let mut paths = Vec::with_capacity(selected.len());
    let mut rejected = Vec::new();
    for source in selected {
        let path = root.join(source);
        let reason = match fs::metadata(&path) {
            Ok(metadata) if metadata.is_file() => None,
            Ok(_) => Some("selected input is not a file".to_owned()),
            Err(error) => Some(format!("{} (kind={:?})", error, error.kind())),
        };
        if let Some(reason) = reason {
            rejected.push(RejectedInput { path, reason });
        } else {
            paths.push(path);
        }
    }
    if rejected.is_empty() {
        Ok(paths)
    } else {
        Err(SelectedInputError { target: target.to_owned(), root: root.to_owned(), rejected })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicU64, Ordering};
    static NEXT: AtomicU64 = AtomicU64::new(0);
    struct Fixture(PathBuf);
    impl Fixture {
        fn new() -> Self {
            let path = std::env::temp_dir().join(format!("simple-selected-c-inputs-{}-{}",
                std::process::id(), NEXT.fetch_add(1, Ordering::Relaxed)));
            fs::create_dir(&path).expect("fresh owned fixture directory");
            Self(path)
        }
        fn source(&self, name: &str) {
            fs::write(self.0.join(name), b"int selected_input(void) { return 1; }\n").unwrap();
        }
    }
    impl Drop for Fixture {
        fn drop(&mut self) { let _ = fs::remove_dir_all(&self.0); }
    }

    #[test]
    fn complete_selection_preserves_exact_order() {
        let fixture = Fixture::new();
        fixture.source("second.c"); fixture.source("first.c");
        let paths = require_selected_c_inputs(&fixture.0, &["second.c", "first.c"], "test-target").unwrap();
        assert_eq!(paths, vec![fixture.0.join("second.c"), fixture.0.join("first.c")]);
    }

    #[test]
    fn partial_selection_reports_every_missing_input_without_returning_partial_job() {
        let fixture = Fixture::new(); fixture.source("present.c");
        let error = require_selected_c_inputs(&fixture.0,
            &["absent-a.c", "present.c", "absent-b.c"], "x86_64-pc-windows-msvc").unwrap_err();
        assert_eq!(error.rejected.iter().map(|item| &item.path).collect::<Vec<_>>(),
                   vec![&fixture.0.join("absent-a.c"), &fixture.0.join("absent-b.c")]);
        assert_eq!(error.target, "x86_64-pc-windows-msvc");
        assert_eq!(error.root, fixture.0);
        let diagnostic = error.to_string();
        assert!(diagnostic.contains("count=2"));
        assert!(diagnostic.contains("absent-a.c") && diagnostic.contains("absent-b.c"));
    }

    #[test]
    fn wholly_missing_selected_inputs_fail_before_archive_construction() {
        let fixture = Fixture::new();
        let error = require_selected_c_inputs(&fixture.0, &["one.c", "two.c"], "test-target").unwrap_err();
        assert_eq!(error.rejected.len(), 2);
    }

    #[test]
    fn one_missing_selected_input_names_the_exact_path() {
        let fixture = Fixture::new(); fixture.source("present.c");
        let error = require_selected_c_inputs(&fixture.0, &["present.c", "missing.c"], "test-target").unwrap_err();
        assert_eq!(error.rejected.len(), 1);
        assert_eq!(error.rejected[0].path, fixture.0.join("missing.c"));
        assert!(error.to_string().contains("runtime-selected-c-inputs-invalid"));
    }

    #[test]
    fn existing_directory_is_not_a_translation_unit() {
        let fixture = Fixture::new(); fs::create_dir(fixture.0.join("directory.c")).unwrap();
        let error = require_selected_c_inputs(&fixture.0, &["directory.c"], "test-target").unwrap_err();
        assert_eq!(error.rejected[0].reason, "selected input is not a file");
    }

    #[test]
    fn unselected_optional_source_is_not_required() {
        let fixture = Fixture::new(); fixture.source("selected.c");
        assert!(!fixture.0.join("optional-other-platform.c").exists());
        assert_eq!(require_selected_c_inputs(&fixture.0, &["selected.c"], "test-target").unwrap(),
                   vec![fixture.0.join("selected.c")]);
    }
}
