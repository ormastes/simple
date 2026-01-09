//! Resource pre-allocation for different application types
//!
//! This module handles resource allocation based on app type, optimizing
//! startup by preparing type-specific resources before main() executes.

use crate::early_startup::{AppType, WindowHints};
use crate::gpu_init::{start_gpu_init, GpuInitHandle, WindowConfig};
use std::io;

/// Pre-allocated resources ready for use by the application
pub struct PreAllocatedResources {
    /// Application type these resources are for
    pub app_type: AppType,
    /// CLI resources (always minimal)
    pub cli: CliResources,
    /// TUI resources (if app_type == Tui)
    pub tui: Option<TuiResources>,
    /// GUI resources (if app_type == Gui)
    pub gui: Option<GuiResources>,
    /// Service resources (if app_type == Service)
    pub service: Option<ServiceResources>,
    /// REPL resources (if app_type == Repl)
    pub repl: Option<ReplResources>,
}

/// Minimal resources for CLI applications
#[derive(Debug, Default)]
pub struct CliResources {
    /// Standard I/O initialized
    pub stdio_ready: bool,
    /// Basic heap allocated
    pub heap_ready: bool,
}

/// Resources for terminal UI applications
#[derive(Debug)]
pub struct TuiResources {
    /// Terminal raw mode enabled
    pub raw_mode_enabled: bool,
    /// Screen buffer allocated
    pub screen_buffer_ready: bool,
    /// Input buffer allocated
    pub input_buffer_ready: bool,
}

/// Resources for graphical applications
pub struct GuiResources {
    /// Window created (may still be initializing)
    pub window_created: bool,
    /// Window handle (platform-specific)
    pub window_handle: Option<usize>,
    /// GPU context initialization started
    pub gpu_init_started: bool,
    /// GPU context ready
    pub gpu_ready: bool,
    /// Event loop thread spawned
    pub event_loop_ready: bool,
    /// GPU initialization handle (for waiting/checking progress)
    gpu_init_handle: Option<GpuInitHandle>,
}

/// Resources for background services
#[derive(Debug)]
pub struct ServiceResources {
    /// Detached from terminal
    pub detached: bool,
    /// Signal handlers installed
    pub signals_ready: bool,
    /// IPC channels created
    pub ipc_ready: bool,
}

/// Resources for REPL applications
#[derive(Debug)]
pub struct ReplResources {
    /// History buffer allocated
    pub history_ready: bool,
    /// Line editor initialized
    pub editor_ready: bool,
    /// Completion engine ready
    pub completion_ready: bool,
}

impl PreAllocatedResources {
    /// Allocate resources based on app type
    pub fn allocate(app_type: AppType, window_hints: &WindowHints) -> io::Result<Self> {
        let cli = CliResources::allocate()?;

        let (tui, gui, service, repl) = match app_type {
            AppType::Cli => (None, None, None, None),
            AppType::Tui => (Some(TuiResources::allocate()?), None, None, None),
            AppType::Gui => (
                None,
                Some(GuiResources::allocate(window_hints)?),
                None,
                None,
            ),
            AppType::Service => (None, None, Some(ServiceResources::allocate()?), None),
            AppType::Repl => (None, None, None, Some(ReplResources::allocate()?)),
        };

        Ok(Self {
            app_type,
            cli,
            tui,
            gui,
            service,
            repl,
        })
    }

    /// Check if all resources are ready
    pub fn is_ready(&self) -> bool {
        match self.app_type {
            AppType::Cli => self.cli.is_ready(),
            AppType::Tui => self.tui.as_ref().map_or(false, |t| t.is_ready()),
            AppType::Gui => self.gui.as_ref().map_or(false, |g| g.is_ready()),
            AppType::Service => self.service.as_ref().map_or(false, |s| s.is_ready()),
            AppType::Repl => self.repl.as_ref().map_or(false, |r| r.is_ready()),
        }
    }
}

// ============================================================================
// CLI Resource Allocation (#1981)
// ============================================================================

impl CliResources {
    /// Allocate minimal resources for CLI applications
    pub fn allocate() -> io::Result<Self> {
        // CLI apps need minimal setup - stdio is already available
        // Just ensure heap is initialized (happens automatically in Rust)
        Ok(Self {
            stdio_ready: true,
            heap_ready: true,
        })
    }

    /// Check if CLI resources are ready
    pub fn is_ready(&self) -> bool {
        self.stdio_ready && self.heap_ready
    }
}

// ============================================================================
// TUI Resource Allocation (#1982)
// ============================================================================

impl TuiResources {
    /// Allocate resources for TUI applications
    pub fn allocate() -> io::Result<Self> {
        #[cfg(feature = "tui")]
        {
            // Enable raw mode for terminal input
            let raw_mode_enabled = crossterm::terminal::enable_raw_mode().is_ok();

            // Screen and input buffers will be allocated by ratatui/crossterm
            // when actually needed, so we just mark them as ready
            Ok(Self {
                raw_mode_enabled,
                screen_buffer_ready: true,
                input_buffer_ready: true,
            })
        }

        #[cfg(not(feature = "tui"))]
        {
            Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "TUI feature not enabled",
            ))
        }
    }

    /// Check if TUI resources are ready
    pub fn is_ready(&self) -> bool {
        self.raw_mode_enabled && self.screen_buffer_ready && self.input_buffer_ready
    }
}

impl Drop for TuiResources {
    fn drop(&mut self) {
        #[cfg(feature = "tui")]
        if self.raw_mode_enabled {
            let _ = crossterm::terminal::disable_raw_mode();
        }
    }
}

// ============================================================================
// GUI Resource Allocation (#1983)
// ============================================================================

impl GuiResources {
    /// Allocate resources for GUI applications
    ///
    /// This starts GPU initialization in the background.
    /// The actual GPU context may not be ready immediately, but will be
    /// initialized asynchronously.
    pub fn allocate(window_hints: &WindowHints) -> io::Result<Self> {
        // Start GPU initialization in background thread
        let config = WindowConfig {
            width: window_hints.width,
            height: window_hints.height,
            title: window_hints.title.clone(),
        };

        let gpu_handle = start_gpu_init(config);

        Ok(Self {
            window_created: true, // Window creation starts immediately
            window_handle: None,  // Will be filled when init completes
            gpu_init_started: true,
            gpu_ready: false, // Will be set when init completes
            event_loop_ready: false,
            gpu_init_handle: Some(gpu_handle),
        })
    }

    /// Check if GUI resources are ready
    pub fn is_ready(&self) -> bool {
        self.gpu_init_handle
            .as_ref()
            .map_or(false, |h| h.is_ready())
    }

    /// Check if window is created (may not have GPU context yet)
    pub fn window_ready(&self) -> bool {
        self.window_created
    }

    /// Wait for GPU initialization to complete
    pub fn wait_gpu(&mut self) -> Result<(), String> {
        if let Some(handle) = self.gpu_init_handle.take() {
            let context = handle.wait()?;
            self.window_handle = Some(context.window_handle);
            self.gpu_ready = true;
            self.event_loop_ready = true;
            Ok(())
        } else {
            Err("GPU initialization already waited".to_string())
        }
    }

    /// Get current GPU initialization progress (0-100)
    pub fn gpu_progress(&self) -> u8 {
        self.gpu_init_handle
            .as_ref()
            .map_or(100, |h| h.state().progress())
    }
}

// ============================================================================
// Service Resource Allocation (#1984)
// ============================================================================

impl ServiceResources {
    /// Allocate resources for service/daemon applications
    pub fn allocate() -> io::Result<Self> {
        #[cfg(unix)]
        {
            // On Unix, we would:
            // 1. Fork and exit parent (daemonize)
            // 2. Create new session (setsid)
            // 3. Change working directory to /
            // 4. Close stdin/stdout/stderr
            // 5. Install signal handlers

            // For now, just mark as ready without actually daemonizing
            // (actual daemonization should be opt-in via flag)
            Ok(Self {
                detached: false,     // Would be true after fork
                signals_ready: true, // Signal handlers would be installed
                ipc_ready: true,     // IPC channels would be created
            })
        }

        #[cfg(windows)]
        {
            // On Windows, we would:
            // 1. Register as Windows Service
            // 2. Set up service control handler
            // 3. Create named pipes for IPC

            Ok(Self {
                detached: false,
                signals_ready: true,
                ipc_ready: true,
            })
        }
    }

    /// Check if service resources are ready
    pub fn is_ready(&self) -> bool {
        self.signals_ready && self.ipc_ready
    }
}

// ============================================================================
// REPL Resource Allocation
// ============================================================================

impl ReplResources {
    /// Allocate resources for REPL applications
    pub fn allocate() -> io::Result<Self> {
        // Rustyline will handle most of this internally
        // We just need to ensure we're ready to create an Editor when needed
        Ok(Self {
            history_ready: true,
            editor_ready: true,
            completion_ready: true,
        })
    }

    /// Check if REPL resources are ready
    pub fn is_ready(&self) -> bool {
        self.history_ready && self.editor_ready && self.completion_ready
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cli_resources() {
        let resources = CliResources::allocate().unwrap();
        assert!(resources.is_ready());
        assert!(resources.stdio_ready);
        assert!(resources.heap_ready);
    }

    #[test]
    fn test_preallocated_resources_cli() {
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
    fn test_preallocated_resources_repl() {
        let hints = WindowHints::default();
        let resources = PreAllocatedResources::allocate(AppType::Repl, &hints).unwrap();

        assert_eq!(resources.app_type, AppType::Repl);
        assert!(resources.repl.is_some());
        assert!(resources.tui.is_none());
        assert!(resources.gui.is_none());
    }

    #[test]
    #[cfg(feature = "tui")]
    fn test_tui_resources() {
        let resources = TuiResources::allocate().unwrap();
        // Raw mode should be enabled
        assert!(resources.raw_mode_enabled);
    }

    #[test]
    #[ignore = "GPU initialization timing varies by environment"]
    fn test_gui_resources() {
        let hints = WindowHints {
            width: 1920,
            height: 1080,
            title: "Test".to_string(),
        };

        let mut resources = GuiResources::allocate(&hints).unwrap();
        // Window creation should start immediately
        assert!(resources.window_created);
        assert!(resources.gpu_init_started);

        // GPU initialization runs in background, may not be ready yet
        // Wait for it to complete
        resources.wait_gpu().unwrap();
        assert!(resources.gpu_ready);
        assert!(resources.is_ready());
    }

    #[test]
    fn test_service_resources() {
        let resources = ServiceResources::allocate().unwrap();
        // For stub implementation, signals and IPC should be marked ready
        assert!(resources.signals_ready);
        assert!(resources.ipc_ready);
    }
}
