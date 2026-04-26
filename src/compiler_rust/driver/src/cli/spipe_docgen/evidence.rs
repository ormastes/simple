//! Evidence discovery for generated SPipe documentation.

use std::fs;
use std::path::{Path, PathBuf};

use super::types::SspecDoc;

const SCREENSHOT_ROOT: &str = "doc/spec/image";
const ARTIFACT_ROOT: &str = "build/test-artifacts";

pub fn enrich_with_discovered_evidence(spipe_doc: &mut SspecDoc) {
    let mut screenshots = Vec::new();
    let mut tui_captures = Vec::new();
    let mut logs = Vec::new();
    let mut artifacts = Vec::new();

    collect_evidence_files(
        &screenshot_dir_for_spec(&spipe_doc.file_path),
        &mut screenshots,
        &mut tui_captures,
        &mut logs,
        &mut artifacts,
    );
    collect_evidence_files(
        &artifact_dir_for_spec(&spipe_doc.file_path),
        &mut screenshots,
        &mut tui_captures,
        &mut logs,
        &mut artifacts,
    );

    screenshots.sort();
    screenshots.dedup();
    tui_captures.sort();
    tui_captures.dedup();
    logs.sort();
    logs.dedup();
    artifacts.sort();
    artifacts.dedup();

    if spipe_doc.metadata.screenshots.is_empty() {
        spipe_doc.metadata.screenshots = screenshots;
    }
    if spipe_doc.metadata.tui_captures.is_empty() {
        spipe_doc.metadata.tui_captures = tui_captures;
    }
    if spipe_doc.metadata.logs.is_empty() {
        spipe_doc.metadata.logs = logs;
    }
    if spipe_doc.metadata.artifacts.is_empty() {
        spipe_doc.metadata.artifacts = artifacts;
    }
}

fn screenshot_dir_for_spec(spec_path: &Path) -> PathBuf {
    PathBuf::from(SCREENSHOT_ROOT).join(spec_relative_dir(spec_path))
}

fn artifact_dir_for_spec(spec_path: &Path) -> PathBuf {
    PathBuf::from(ARTIFACT_ROOT).join(spec_relative_dir(spec_path))
}

fn spec_relative_dir(spec_path: &Path) -> String {
    spec_path
        .to_string_lossy()
        .replace("simple/std_lib/test/", "")
        .replace("test/", "")
        .replace("_spec.spl", "")
        .replace("_test.spl", "")
        .replace(".spl", "")
}

fn collect_evidence_files(
    evidence_dir: &Path,
    screenshots: &mut Vec<String>,
    tui_captures: &mut Vec<String>,
    logs: &mut Vec<String>,
    artifacts: &mut Vec<String>,
) {
    if !evidence_dir.exists() || !evidence_dir.is_dir() {
        return;
    }

    let entries = match fs::read_dir(evidence_dir) {
        Ok(entries) => entries,
        Err(_) => return,
    };

    for entry in entries.flatten() {
        let path = entry.path();
        if !path.is_file() {
            continue;
        }

        let rel = normalize_rel_path(&path);
        let ext = path
            .extension()
            .and_then(|s| s.to_str())
            .map(|s| s.to_ascii_lowercase())
            .unwrap_or_default();

        match ext.as_str() {
            "png" | "jpg" | "jpeg" | "webp" => screenshots.push(rel),
            "ansi" => tui_captures.push(rel),
            "log" => logs.push(rel),
            "json" | "txt" | "html" | "svg" => artifacts.push(rel),
            _ => {}
        }
    }
}

fn normalize_rel_path(path: &Path) -> String {
    path.to_string_lossy().replace('\\', "/")
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::types::FeatureMetadata;
    use std::fs;
    use std::path::PathBuf;
    use std::sync::{Mutex, OnceLock};

    use tempfile::tempdir;

    fn cwd_lock() -> &'static Mutex<()> {
        static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
        LOCK.get_or_init(|| Mutex::new(()))
    }

    struct CurrentDirGuard {
        previous: PathBuf,
    }

    impl Drop for CurrentDirGuard {
        fn drop(&mut self) {
            let _ = std::env::set_current_dir(&self.previous);
        }
    }

    fn with_temp_cwd() -> (tempfile::TempDir, CurrentDirGuard) {
        let tempdir = tempdir().expect("tempdir");
        let previous = std::env::current_dir().expect("current dir");
        std::env::set_current_dir(tempdir.path()).expect("set current dir");
        (tempdir, CurrentDirGuard { previous })
    }

    #[test]
    fn test_screenshot_dir_for_regular_spec_path() {
        let dir = screenshot_dir_for_spec(Path::new("test/app/web_dashboard/tmux_rest_api_spec.spl"));
        assert_eq!(
            dir.to_string_lossy().replace('\\', "/"),
            "doc/spec/image/app/web_dashboard/tmux_rest_api"
        );
    }

    #[test]
    fn test_artifact_dir_for_regular_spec_path() {
        let dir = artifact_dir_for_spec(Path::new("test/app/web_dashboard/tmux_rest_api_spec.spl"));
        assert_eq!(
            dir.to_string_lossy().replace('\\', "/"),
            "build/test-artifacts/app/web_dashboard/tmux_rest_api"
        );
    }

    #[test]
    fn test_enrich_with_discovered_evidence_discovers_and_preserves_explicit_metadata() {
        let _guard = cwd_lock().lock().expect("lock cwd");
        let (_tempdir, _cwd_guard) = with_temp_cwd();

        let screenshot_path = PathBuf::from("doc/spec/image/app/web_dashboard/tmux_rest_api/shot.png");
        let tui_path = PathBuf::from("build/test-artifacts/app/web_dashboard/tmux_rest_api/terminal.ansi");
        let log_path = PathBuf::from("build/test-artifacts/app/web_dashboard/tmux_rest_api/run.log");
        let artifact_json_path = PathBuf::from("build/test-artifacts/app/web_dashboard/tmux_rest_api/result.json");
        let artifact_txt_path = PathBuf::from("build/test-artifacts/app/web_dashboard/tmux_rest_api/notes.txt");

        for path in [
            &screenshot_path,
            &tui_path,
            &log_path,
            &artifact_json_path,
            &artifact_txt_path,
        ] {
            fs::create_dir_all(path.parent().expect("parent dir")).expect("create dir");
        }

        fs::write(&screenshot_path, b"png").expect("write screenshot");
        fs::write(&tui_path, b"ansi").expect("write tui");
        fs::write(&log_path, b"log").expect("write log");
        fs::write(&artifact_json_path, b"{}").expect("write json");
        fs::write(&artifact_txt_path, b"notes").expect("write txt");

        let mut doc = SspecDoc {
            file_path: PathBuf::from("test/app/web_dashboard/tmux_rest_api_spec.spl"),
            raw_content: String::new(),
            doc_blocks: vec![],
            feature_title: None,
            feature_ids: vec![],
            metadata: FeatureMetadata {
                logs: vec!["explicit/log.txt".to_string()],
                ..Default::default()
            },
        };

        enrich_with_discovered_evidence(&mut doc);

        let screenshot_expected = std::env::current_dir()
            .expect("current dir")
            .join(&screenshot_path)
            .to_string_lossy()
            .replace('\\', "/");
        let tui_expected = std::env::current_dir()
            .expect("current dir")
            .join(&tui_path)
            .to_string_lossy()
            .replace('\\', "/");
        let log_expected = vec!["explicit/log.txt".to_string()];
        let artifact_json_expected = std::env::current_dir()
            .expect("current dir")
            .join(&artifact_json_path)
            .to_string_lossy()
            .replace('\\', "/");
        let artifact_txt_expected = std::env::current_dir()
            .expect("current dir")
            .join(&artifact_txt_path)
            .to_string_lossy()
            .replace('\\', "/");

        assert_eq!(doc.metadata.screenshots, vec![screenshot_expected]);
        assert_eq!(doc.metadata.tui_captures, vec![tui_expected]);
        assert_eq!(doc.metadata.logs, log_expected);
        assert_eq!(
            doc.metadata.artifacts,
            vec![artifact_json_expected, artifact_txt_expected]
        );
    }
}
