use std::collections::HashSet;
use std::path::{Path, PathBuf};
use std::sync::mpsc::channel;

use notify::{Config, EventKind, RecommendedWatcher, RecursiveMode, Watcher};

use crate::dependency_cache::{analyze_source, current_mtime, BuildCache, DepInfo};
use crate::runner::Runner;

/// Watch a source file and its dependencies, recompiling and rerunning on change.
pub fn watch(entry: &Path, verbose: bool) -> Result<(), String> {
    let runner = Runner::new();
    let mut cache = BuildCache::load();

    // Initial build
    rebuild(entry, &runner, &mut cache, verbose)?;

    // Set up filesystem watch
    let (tx, rx) = channel();
    let mut watcher: RecommendedWatcher =
        RecommendedWatcher::new(tx, Config::default()).map_err(|e| format!("watch init: {e}"))?;

    // Watch the entry directory
    let watch_path = entry
        .parent()
        .map(Path::to_path_buf)
        .unwrap_or_else(|| PathBuf::from("."));
    watcher
        .watch(&watch_path, RecursiveMode::Recursive)
        .map_err(|e| format!("watch path: {e}"))?;

    if verbose {
        println!("Watching {} (and dependencies)...", entry.display());
    }

    loop {
        match rx.recv() {
            Ok(Ok(event)) => {
                if !matches!(
                    event.kind,
                    EventKind::Modify(_) | EventKind::Create(_) | EventKind::Remove(_)
                ) {
                    continue;
                }
                let changed: Vec<PathBuf> = event.paths.into_iter().collect();
                if verbose {
                    for p in &changed {
                        println!("Change detected: {}", p.display());
                    }
                }
                let mut affected: HashSet<PathBuf> = HashSet::new();
                for path in &changed {
                    affected.insert(path.clone());
                    for dep in cache.dependents_of(path) {
                        affected.insert(dep);
                    }
                }

                for src in affected {
                    if src.extension().and_then(|e| e.to_str()) == Some("spl") {
                        if verbose {
                            println!("Rebuilding {}", src.display());
                        }
                        let _ = rebuild(&src, &runner, &mut cache, verbose);
                    }
                }
            }
            Ok(Err(e)) => {
                if verbose {
                    eprintln!("watch error: {e}");
                }
            }
            Err(_) => break,
        }
    }

    Ok(())
}

fn rebuild(source: &Path, runner: &Runner, cache: &mut BuildCache, verbose: bool) -> Result<(), String> {
    // Output SMF files to .simple/build/ directory
    let parent = source.parent().unwrap_or(Path::new("."));
    let build_dir = parent.join(".simple").join("build");
    std::fs::create_dir_all(&build_dir).map_err(|e| format!("create build dir: {e}"))?;

    let file_stem = source
        .file_stem()
        .ok_or_else(|| "source has no file stem".to_string())?;
    let out = build_dir.join(file_stem).with_extension("smf");

    runner.compile_file(source, &out)?;

    // Update dependency info
    let (deps, macros) = analyze_source(source).map_err(|e| format!("analyze deps: {e}"))?;
    let info = DepInfo {
        source: source.to_path_buf(),
        output: out,
        dependencies: deps.clone(),
        macros,
        mtime: current_mtime(source),
    };
    cache.update(info);
    cache.save();

    if verbose {
        println!(
            "Updated cache for {} (deps: {}, macros: {})",
            source.display(),
            deps.len(),
            cache.get(source).map(|i| i.macros.len()).unwrap_or(0)
        );
    }

    Ok(())
}
