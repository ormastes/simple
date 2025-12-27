//! Tests for startup optimization features (#1970-#1991)
//!
//! This test suite verifies:
//! - Phase 1: Early argument parsing (#1970-#1976)
//! - Phase 1: File prefetching (mmap + madvise/PrefetchVirtualMemory)
//! - Phase 1: App type detection
//! - Phase 1: Window hints parsing
//! - Phase 2: Resource pre-allocation (#1981-#1984)
//! - Phase 3: GPU initialization (#1987-#1991)

use simple_driver::{
    display_loading_indicator, parse_early_args, prefetch_file, prefetch_files, start_gpu_init,
    AppType, EarlyConfig, GpuInitPhase, GpuInitState, PreAllocatedResources, StartupEvent,
    StartupProgress, WindowConfig, WindowHints,
};
use std::fs::File;
use std::io::Write;
use tempfile::{tempdir, NamedTempFile};

#[test]
fn test_early_args_default() {
    let args: Vec<&str> = vec![];
    let config = parse_early_args(args);

    assert_eq!(config.app_type, AppType::Cli);
    assert!(config.enable_prefetch);
    assert_eq!(config.input_files.len(), 0);
    assert_eq!(config.window_hints.width, 1280);
    assert_eq!(config.window_hints.height, 720);
}

#[test]
fn test_early_args_app_type_cli() {
    let args = vec!["--app-type", "cli"];
    let config = parse_early_args(args);

    assert_eq!(config.app_type, AppType::Cli);
}

#[test]
fn test_early_args_app_type_gui() {
    let args = vec!["--app-type", "gui"];
    let config = parse_early_args(args);

    assert_eq!(config.app_type, AppType::Gui);
}

#[test]
fn test_early_args_app_type_tui() {
    let args = vec!["--app-type", "tui"];
    let config = parse_early_args(args);

    assert_eq!(config.app_type, AppType::Tui);
}

#[test]
fn test_early_args_app_type_service() {
    let args = vec!["--app-type", "service"];
    let config = parse_early_args(args);

    assert_eq!(config.app_type, AppType::Service);
}

#[test]
fn test_early_args_app_type_repl() {
    let args = vec!["--app-type", "repl"];
    let config = parse_early_args(args);

    assert_eq!(config.app_type, AppType::Repl);
}

#[test]
fn test_early_args_window_hints() {
    let args = vec![
        "--window-width", "1920",
        "--window-height", "1080",
        "--window-title", "Test Window",
    ];
    let config = parse_early_args(args);

    assert_eq!(config.window_hints.width, 1920);
    assert_eq!(config.window_hints.height, 1080);
    assert_eq!(config.window_hints.title, "Test Window");
}

#[test]
fn test_early_args_prefetch_disabled() {
    let args = vec!["--no-prefetch"];
    let config = parse_early_args(args);

    assert!(!config.enable_prefetch);
}

#[test]
fn test_early_args_file_detection() {
    // Create a temporary file
    let mut temp_file = NamedTempFile::new().unwrap();
    temp_file.write_all(b"test content").unwrap();
    temp_file.flush().unwrap();

    let path_str = temp_file.path().to_str().unwrap();
    let args = vec![path_str];
    let config = parse_early_args(args);

    // File should be detected and added to input_files
    assert_eq!(config.input_files.len(), 1);
    assert_eq!(config.input_files[0], temp_file.path());

    // Should also be in remaining_args for later processing
    assert_eq!(config.remaining_args.len(), 1);
}

#[test]
fn test_early_args_multiple_files() {
    let dir = tempdir().unwrap();

    // Create multiple files
    let file1 = dir.path().join("test1.spl");
    let file2 = dir.path().join("test2.spl");

    File::create(&file1).unwrap().write_all(b"file1").unwrap();
    File::create(&file2).unwrap().write_all(b"file2").unwrap();

    let args = vec![
        file1.to_str().unwrap(),
        file2.to_str().unwrap(),
    ];
    let config = parse_early_args(args);

    assert_eq!(config.input_files.len(), 2);
    assert!(config.input_files.contains(&file1));
    assert!(config.input_files.contains(&file2));
}

#[test]
fn test_early_args_nonexistent_file() {
    let args = vec!["/nonexistent/file.spl"];
    let config = parse_early_args(args);

    // Nonexistent files should not be added to input_files
    assert_eq!(config.input_files.len(), 0);

    // But should still be in remaining_args
    assert_eq!(config.remaining_args.len(), 1);
}

#[test]
fn test_early_args_combined() {
    let mut temp_file = NamedTempFile::new().unwrap();
    temp_file.write_all(b"test").unwrap();
    temp_file.flush().unwrap();

    let args = vec![
        "--app-type", "gui",
        "--window-width", "1024",
        "--window-height", "768",
        temp_file.path().to_str().unwrap(),
        "--unknown-flag",
        "value",
    ];
    let config = parse_early_args(args);

    assert_eq!(config.app_type, AppType::Gui);
    assert_eq!(config.window_hints.width, 1024);
    assert_eq!(config.window_hints.height, 768);
    assert_eq!(config.input_files.len(), 1);

    // Unknown flags and file should be in remaining_args
    assert!(config.remaining_args.len() >= 3);
}

#[test]
fn test_prefetch_single_file() {
    let mut temp_file = NamedTempFile::new().unwrap();
    let test_data = b"Prefetch test data";
    temp_file.write_all(test_data).unwrap();
    temp_file.flush().unwrap();

    // Prefetch the file
    let handle = prefetch_file(temp_file.path()).unwrap();

    // Wait for prefetch to complete
    handle.wait().unwrap();

    // File should still be readable
    let content = std::fs::read(temp_file.path()).unwrap();
    assert_eq!(&content, test_data);
}

#[test]
fn test_prefetch_multiple_files() {
    let dir = tempdir().unwrap();

    // Create multiple files
    let files: Vec<_> = (0..5)
        .map(|i| {
            let path = dir.path().join(format!("file{}.dat", i));
            let mut file = File::create(&path).unwrap();
            file.write_all(format!("Content {}", i).as_bytes()).unwrap();
            path
        })
        .collect();

    // Prefetch all files
    let handle = prefetch_files(&files).unwrap();

    // Wait for prefetch to complete
    handle.wait().unwrap();

    // All files should still be readable
    for (i, path) in files.iter().enumerate() {
        let content = std::fs::read(path).unwrap();
        let expected = format!("Content {}", i);
        assert_eq!(content, expected.as_bytes());
    }
}

#[test]
fn test_prefetch_large_file() {
    let mut temp_file = NamedTempFile::new().unwrap();

    // Create a 1MB file
    let data = vec![0xAB; 1024 * 1024];
    temp_file.write_all(&data).unwrap();
    temp_file.flush().unwrap();

    // Prefetch the file
    let handle = prefetch_file(temp_file.path()).unwrap();
    handle.wait().unwrap();

    // Verify content
    let content = std::fs::read(temp_file.path()).unwrap();
    assert_eq!(content.len(), 1024 * 1024);
    assert_eq!(&content[0..10], &data[0..10]);
}

#[test]
fn test_prefetch_empty_file() {
    let temp_file = NamedTempFile::new().unwrap();

    // Prefetch empty file (should not error)
    let handle = prefetch_file(temp_file.path()).unwrap();
    handle.wait().unwrap();
}

#[test]
fn test_prefetch_nonexistent_file() {
    // Prefetching nonexistent file should return error
    let result = prefetch_file("/nonexistent/file/path");
    assert!(result.is_err());
}

#[test]
fn test_app_type_string_conversion() {
    assert_eq!(AppType::Cli.as_str(), "cli");
    assert_eq!(AppType::Tui.as_str(), "tui");
    assert_eq!(AppType::Gui.as_str(), "gui");
    assert_eq!(AppType::Service.as_str(), "service");
    assert_eq!(AppType::Repl.as_str(), "repl");

    assert_eq!(AppType::from_str("cli"), Some(AppType::Cli));
    assert_eq!(AppType::from_str("tui"), Some(AppType::Tui));
    assert_eq!(AppType::from_str("gui"), Some(AppType::Gui));
    assert_eq!(AppType::from_str("service"), Some(AppType::Service));
    assert_eq!(AppType::from_str("repl"), Some(AppType::Repl));
    assert_eq!(AppType::from_str("invalid"), None);
}

#[test]
fn test_window_hints_default() {
    use simple_driver::WindowHints;

    let hints = WindowHints::default();
    assert_eq!(hints.width, 1280);
    assert_eq!(hints.height, 720);
    assert_eq!(hints.title, "Simple Application");
}

#[test]
fn test_early_config_default() {
    let config = EarlyConfig::default();

    assert_eq!(config.app_type, AppType::Cli);
    assert!(config.enable_prefetch);
    assert_eq!(config.input_files.len(), 0);
    assert_eq!(config.remaining_args.len(), 0);
    assert_eq!(config.window_hints.width, 1280);
    assert_eq!(config.window_hints.height, 720);
}

// ============================================================================
// Phase 2: Resource Pre-Allocation Tests (#1981-#1984)
// ============================================================================

#[test]
fn test_resource_allocation_cli() {
    let hints = WindowHints::default();
    let resources = PreAllocatedResources::allocate(AppType::Cli, &hints).unwrap();

    assert_eq!(resources.app_type, AppType::Cli);
    assert!(resources.cli.is_ready());
    assert!(resources.tui.is_none());
    assert!(resources.gui.is_none());
    assert!(resources.service.is_none());
    assert!(resources.repl.is_none());
}

#[test]
fn test_resource_allocation_tui() {
    let hints = WindowHints::default();

    #[cfg(feature = "tui")]
    {
        let resources = PreAllocatedResources::allocate(AppType::Tui, &hints).unwrap();

        assert_eq!(resources.app_type, AppType::Tui);
        assert!(resources.tui.is_some());
        let tui = resources.tui.as_ref().unwrap();
        assert!(tui.raw_mode_enabled);
    }

    #[cfg(not(feature = "tui"))]
    {
        let result = PreAllocatedResources::allocate(AppType::Tui, &hints);
        assert!(result.is_err());
    }
}

#[test]
fn test_resource_allocation_gui() {
    let hints = WindowHints {
        width: 1920,
        height: 1080,
        title: "Test GUI".to_string(),
    };

    let resources = PreAllocatedResources::allocate(AppType::Gui, &hints).unwrap();

    assert_eq!(resources.app_type, AppType::Gui);
    assert!(resources.gui.is_some());
    // Window creation is stubbed for now
    // let gui = resources.gui.as_ref().unwrap();
    // assert!(!gui.window_created); // Stub implementation
}

#[test]
fn test_resource_allocation_service() {
    let hints = WindowHints::default();
    let resources = PreAllocatedResources::allocate(AppType::Service, &hints).unwrap();

    assert_eq!(resources.app_type, AppType::Service);
    assert!(resources.service.is_some());
    let service = resources.service.as_ref().unwrap();
    assert!(service.signals_ready);
    assert!(service.ipc_ready);
}

#[test]
fn test_resource_allocation_repl() {
    let hints = WindowHints::default();
    let resources = PreAllocatedResources::allocate(AppType::Repl, &hints).unwrap();

    assert_eq!(resources.app_type, AppType::Repl);
    assert!(resources.repl.is_some());
    let repl = resources.repl.as_ref().unwrap();
    assert!(repl.history_ready);
    assert!(repl.editor_ready);
    assert!(repl.completion_ready);
}

#[test]
fn test_cli_resources_ready() {
    use simple_driver::CliResources;

    let resources = CliResources::allocate().unwrap();
    assert!(resources.is_ready());
}

#[test]
fn test_repl_resources_ready() {
    use simple_driver::ReplResources;

    let resources = ReplResources::allocate().unwrap();
    assert!(resources.is_ready());
}

#[test]
fn test_service_resources_ready() {
    use simple_driver::ServiceResources;

    let resources = ServiceResources::allocate().unwrap();
    assert!(resources.is_ready());
}

// ============================================================================
// Integration Tests: Full Startup Flow
// ============================================================================

#[test]
fn test_full_startup_flow_cli() {
    // Simulate full startup for CLI app
    let args = vec!["test.spl"];
    let config = parse_early_args(args);

    let resources = PreAllocatedResources::allocate(config.app_type, &config.window_hints).unwrap();

    assert_eq!(config.app_type, AppType::Cli);
    assert!(resources.is_ready());
}

#[test]
fn test_full_startup_flow_gui() {
    // Simulate full startup for GUI app
    let args = vec![
        "--app-type", "gui",
        "--window-width", "1024",
        "--window-height", "768",
        "app.spl",
    ];
    let config = parse_early_args(args);

    let resources = PreAllocatedResources::allocate(config.app_type, &config.window_hints).unwrap();

    assert_eq!(config.app_type, AppType::Gui);
    assert_eq!(config.window_hints.width, 1024);
    assert_eq!(config.window_hints.height, 768);
}

#[test]
fn test_full_startup_flow_with_prefetch() {
    let mut temp_file = NamedTempFile::new().unwrap();
    temp_file.write_all(b"test code").unwrap();
    temp_file.flush().unwrap();

    let path_str = temp_file.path().to_str().unwrap();
    let args = vec!["--app-type", "cli", path_str];

    // Phase 1: Early arg parsing
    let config = parse_early_args(args);

    // Start prefetch
    let handle = if !config.input_files.is_empty() {
        prefetch_files(&config.input_files).ok()
    } else {
        None
    };

    // Pre-allocate resources
    let resources = PreAllocatedResources::allocate(config.app_type, &config.window_hints).unwrap();

    // Wait for prefetch
    if let Some(h) = handle {
        h.wait().unwrap();
    }

    // Verify
    assert_eq!(config.input_files.len(), 1);
    assert!(resources.is_ready());
}

// ============================================================================
// Phase 3: GPU Initialization Tests (#1987-#1991)
// ============================================================================

#[test]
fn test_gpu_init_state() {
    let state = GpuInitState::new();

    assert_eq!(state.phase(), GpuInitPhase::Idle);
    assert!(!state.is_ready());
    assert_eq!(state.progress(), 0);
}

#[test]
fn test_gpu_init_handle() {
    let config = WindowConfig {
        width: 1024,
        height: 768,
        title: "Test GPU Init".to_string(),
    };

    let handle = start_gpu_init(config);

    // Should not be ready immediately
    assert!(!handle.is_ready());

    // Get state
    let state = handle.state();
    assert!(state.progress() <= 100);

    // Wait for completion
    let result = handle.wait();
    assert!(result.is_ok());

    let context = result.unwrap();
    assert_eq!(context.width, 1024);
    assert_eq!(context.height, 768);
}

#[test]
fn test_loading_indicator() {
    let state = GpuInitState::new();

    let msg = display_loading_indicator(&state);
    assert!(msg.contains("0%"));
    assert!(msg.contains("Idle"));
}

#[test]
fn test_startup_progress_events() {
    let progress = StartupProgress::new();

    progress.emit(StartupEvent::EarlyStartup);
    progress.emit(StartupEvent::PrefetchStarted { file_count: 3 });
    progress.emit(StartupEvent::GpuInitStarted {
        width: 1920,
        height: 1080,
    });

    let events = progress.events();
    assert_eq!(events.len(), 3);

    let latest = progress.latest();
    assert!(matches!(latest, Some(StartupEvent::GpuInitStarted { .. })));
}

#[test]
fn test_gpu_resources_with_init() {
    let hints = WindowHints {
        width: 800,
        height: 600,
        title: "Test".to_string(),
    };

    let resources = PreAllocatedResources::allocate(AppType::Gui, &hints).unwrap();

    assert_eq!(resources.app_type, AppType::Gui);
    assert!(resources.gui.is_some());

    let gui = resources.gui.as_ref().unwrap();
    assert!(gui.window_created);
    assert!(gui.gpu_init_started);

    // GPU progress should be available
    let progress = gui.gpu_progress();
    assert!(progress <= 100);
}

#[test]
fn test_full_gui_startup_flow() {
    let args = vec![
        "--app-type",
        "gui",
        "--window-width",
        "1280",
        "--window-height",
        "720",
        "--window-title",
        "My GUI App",
    ];

    // Phase 1: Parse args
    let config = parse_early_args(args);
    assert_eq!(config.app_type, AppType::Gui);
    assert_eq!(config.window_hints.width, 1280);
    assert_eq!(config.window_hints.height, 720);

    // Phase 2: Allocate resources (starts GPU init)
    let resources = PreAllocatedResources::allocate(config.app_type, &config.window_hints).unwrap();

    assert!(resources.gui.is_some());
    let gui = resources.gui.as_ref().unwrap();
    assert!(gui.window_created);
    assert!(gui.gpu_init_started);
}

#[test]
fn test_startup_event_variants() {
    let progress = StartupProgress::new();

    // Test all event variants
    progress.emit(StartupEvent::EarlyStartup);
    progress.emit(StartupEvent::PrefetchStarted { file_count: 5 });
    progress.emit(StartupEvent::PrefetchCompleted);
    progress.emit(StartupEvent::ResourceAllocationStarted {
        app_type: "gui".to_string(),
    });
    progress.emit(StartupEvent::ResourceAllocationCompleted);
    progress.emit(StartupEvent::GpuInitStarted {
        width: 1920,
        height: 1080,
    });
    progress.emit(StartupEvent::GpuInitProgress {
        phase: "Creating window".to_string(),
        progress: 25,
    });
    progress.emit(StartupEvent::GpuInitCompleted);
    progress.emit(StartupEvent::RuntimeInitStarted);
    progress.emit(StartupEvent::RuntimeInitCompleted);
    progress.emit(StartupEvent::ReadyToRun);

    let events = progress.events();
    assert_eq!(events.len(), 11);
}
