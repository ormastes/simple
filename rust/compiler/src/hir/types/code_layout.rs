//! Code locality layout types for 4KB page optimization.
//!
//! This module defines the layout phase taxonomy used to group functions
//! by their execution timing, enabling optimal code placement within 4KB pages
//! for better startup performance and cache locality.
//!
//! # Phase Taxonomy
//!
//! - **Startup**: Code executed from process entry to main loop entry
//! - **FirstFrame**: Code executed from main loop entry to first render/"ready"
//! - **Steady**: Hot paths during steady-state execution (event handling, rendering)
//! - **Cold**: Rarely executed code (help, error handling, seldom-used features)
//!
//! # Example
//!
//! ```simple
//! #[layout(phase="startup")]
//! fn parse_args(argv: []str) -> Args:
//!     ...
//!
//! #[layout(phase="first_frame")]
//! fn render_first_frame(ui: Ui):
//!     ...
//!
//! #[layout(anchor="event_loop")]
//! fn event_loop(app: App):
//!     ...
//! ```

use std::fmt;

/// Layout phase for code locality optimization.
///
/// Functions are grouped by their execution phase to minimize
/// the number of distinct 4KB pages touched during startup.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum LayoutPhase {
    /// Code executed from process entry to main loop entry.
    /// Highest priority for early placement in binary.
    Startup,

    /// Code executed from main loop entry to first render/"ready".
    /// Second priority, placed after startup code.
    FirstFrame,

    /// Hot paths during steady-state execution.
    /// Event handling, rendering, frequently-called functions.
    #[default]
    Steady,

    /// Rarely executed code.
    /// Help text, error handling, seldom-used features.
    Cold,
}

impl LayoutPhase {
    /// Parse layout phase from string.
    pub fn from_str(s: &str) -> Option<Self> {
        match s.to_lowercase().as_str() {
            "startup" => Some(LayoutPhase::Startup),
            "first_frame" | "firstframe" => Some(LayoutPhase::FirstFrame),
            "steady" => Some(LayoutPhase::Steady),
            "cold" => Some(LayoutPhase::Cold),
            _ => None,
        }
    }

    /// Get the string representation for this phase.
    pub fn as_str(&self) -> &'static str {
        match self {
            LayoutPhase::Startup => "startup",
            LayoutPhase::FirstFrame => "first_frame",
            LayoutPhase::Steady => "steady",
            LayoutPhase::Cold => "cold",
        }
    }

    /// Get the priority order (lower = earlier in binary).
    pub fn priority(&self) -> u8 {
        match self {
            LayoutPhase::Startup => 0,
            LayoutPhase::FirstFrame => 1,
            LayoutPhase::Steady => 2,
            LayoutPhase::Cold => 3,
        }
    }

    /// Get the ELF section suffix for this phase.
    /// Used when emitting functions to phase-specific sections.
    pub fn section_suffix(&self) -> &'static str {
        match self {
            LayoutPhase::Startup => ".spl.startup",
            LayoutPhase::FirstFrame => ".spl.first_frame",
            LayoutPhase::Steady => ".spl.steady",
            LayoutPhase::Cold => ".spl.cold",
        }
    }
}

impl fmt::Display for LayoutPhase {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// Layout anchor marking a boundary in execution flow.
///
/// Anchors establish hard boundaries for layout optimization:
/// - `EventLoop`: Marks the main loop entry point. Everything needed before
///   this is a candidate for tight startup packing.
/// - `Ready`: Marks the "first frame rendered" / "UI ready" point.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LayoutAnchor {
    /// Main event loop entry point.
    /// Establishes boundary between startup/first_frame and steady phases.
    EventLoop,

    /// Custom anchor with a user-defined name.
    /// Used with `std.layout.mark("name")` for profiling.
    Custom(String),
}

impl LayoutAnchor {
    /// Parse layout anchor from string.
    pub fn from_str(s: &str) -> Option<Self> {
        match s.to_lowercase().as_str() {
            "event_loop" | "eventloop" | "main_loop" | "mainloop" => Some(LayoutAnchor::EventLoop),
            _ => Some(LayoutAnchor::Custom(s.to_string())),
        }
    }

    /// Get string representation.
    pub fn as_str(&self) -> &str {
        match self {
            LayoutAnchor::EventLoop => "event_loop",
            LayoutAnchor::Custom(name) => name,
        }
    }
}

impl fmt::Display for LayoutAnchor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// Complete layout hint for a function.
///
/// Combines phase classification with optional anchor designation
/// and pinning control.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct FunctionLayoutHint {
    /// The execution phase for this function.
    pub phase: LayoutPhase,

    /// Optional anchor designation (e.g., event_loop).
    pub anchor: Option<LayoutAnchor>,

    /// If true, this function should not be moved from its phase group
    /// even if profile data suggests otherwise.
    pub pinned: bool,
}

impl FunctionLayoutHint {
    /// Create a new layout hint with just a phase.
    pub fn with_phase(phase: LayoutPhase) -> Self {
        Self {
            phase,
            anchor: None,
            pinned: false,
        }
    }

    /// Create a new layout hint with an anchor.
    pub fn with_anchor(anchor: LayoutAnchor) -> Self {
        Self {
            phase: LayoutPhase::Steady, // Anchors default to steady phase
            anchor: Some(anchor),
            pinned: false,
        }
    }

    /// Set the pinned flag.
    pub fn pinned(mut self) -> Self {
        self.pinned = true;
        self
    }

    /// Check if this function is marked as an event loop anchor.
    pub fn is_event_loop(&self) -> bool {
        matches!(self.anchor, Some(LayoutAnchor::EventLoop))
    }
}

/// Page budget configuration for a layout phase.
#[derive(Debug, Clone)]
pub struct PageBudget {
    /// The phase this budget applies to.
    pub phase: LayoutPhase,

    /// Page size in bytes (typically 4096).
    pub page_size: u32,

    /// Maximum number of pages for this phase (0 = unlimited).
    pub max_pages: u32,

    /// Whether to align group boundary to page size.
    pub align_pages: bool,
}

impl Default for PageBudget {
    fn default() -> Self {
        Self {
            phase: LayoutPhase::Steady,
            page_size: 4096,
            max_pages: 0, // Unlimited
            align_pages: false,
        }
    }
}

impl PageBudget {
    /// Create startup phase budget (tight packing).
    pub fn startup(max_pages: u32) -> Self {
        Self {
            phase: LayoutPhase::Startup,
            page_size: 4096,
            max_pages,
            align_pages: true,
        }
    }

    /// Create first_frame phase budget.
    pub fn first_frame(max_pages: u32) -> Self {
        Self {
            phase: LayoutPhase::FirstFrame,
            page_size: 4096,
            max_pages,
            align_pages: true,
        }
    }

    /// Create unlimited steady budget.
    pub fn steady() -> Self {
        Self {
            phase: LayoutPhase::Steady,
            page_size: 4096,
            max_pages: 0,
            align_pages: false,
        }
    }

    /// Create cold phase budget.
    pub fn cold() -> Self {
        Self {
            phase: LayoutPhase::Cold,
            page_size: 4096,
            max_pages: 0,
            align_pages: false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_layout_phase_from_str() {
        assert_eq!(LayoutPhase::from_str("startup"), Some(LayoutPhase::Startup));
        assert_eq!(LayoutPhase::from_str("STARTUP"), Some(LayoutPhase::Startup));
        assert_eq!(LayoutPhase::from_str("first_frame"), Some(LayoutPhase::FirstFrame));
        assert_eq!(LayoutPhase::from_str("firstframe"), Some(LayoutPhase::FirstFrame));
        assert_eq!(LayoutPhase::from_str("steady"), Some(LayoutPhase::Steady));
        assert_eq!(LayoutPhase::from_str("cold"), Some(LayoutPhase::Cold));
        assert_eq!(LayoutPhase::from_str("invalid"), None);
    }

    #[test]
    fn test_layout_phase_priority() {
        assert!(LayoutPhase::Startup.priority() < LayoutPhase::FirstFrame.priority());
        assert!(LayoutPhase::FirstFrame.priority() < LayoutPhase::Steady.priority());
        assert!(LayoutPhase::Steady.priority() < LayoutPhase::Cold.priority());
    }

    #[test]
    fn test_layout_phase_section_suffix() {
        assert_eq!(LayoutPhase::Startup.section_suffix(), ".spl.startup");
        assert_eq!(LayoutPhase::FirstFrame.section_suffix(), ".spl.first_frame");
        assert_eq!(LayoutPhase::Steady.section_suffix(), ".spl.steady");
        assert_eq!(LayoutPhase::Cold.section_suffix(), ".spl.cold");
    }

    #[test]
    fn test_layout_anchor_from_str() {
        assert_eq!(LayoutAnchor::from_str("event_loop"), Some(LayoutAnchor::EventLoop));
        assert_eq!(LayoutAnchor::from_str("main_loop"), Some(LayoutAnchor::EventLoop));
        assert_eq!(
            LayoutAnchor::from_str("custom_marker"),
            Some(LayoutAnchor::Custom("custom_marker".to_string()))
        );
    }

    #[test]
    fn test_function_layout_hint() {
        let hint = FunctionLayoutHint::with_phase(LayoutPhase::Startup).pinned();
        assert_eq!(hint.phase, LayoutPhase::Startup);
        assert!(hint.pinned);
        assert!(!hint.is_event_loop());

        let anchor_hint = FunctionLayoutHint::with_anchor(LayoutAnchor::EventLoop);
        assert!(anchor_hint.is_event_loop());
    }

    #[test]
    fn test_page_budget() {
        let startup = PageBudget::startup(8);
        assert_eq!(startup.phase, LayoutPhase::Startup);
        assert_eq!(startup.max_pages, 8);
        assert!(startup.align_pages);

        let steady = PageBudget::steady();
        assert_eq!(steady.max_pages, 0); // Unlimited
        assert!(!steady.align_pages);
    }
}
