//! Optimization inventory and native build optimization profiles.
//!
//! This module centralizes two things:
//! - the optimization profile surface exposed by the Rust driver for native builds
//! - a human-readable inventory of currently implemented optimization groups

use crate::BuildMode;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeOptimizationLevel {
    None,
    Basic,
    Standard,
    Aggressive,
}

impl NativeOptimizationLevel {
    pub fn parse(value: &str) -> Result<Self, String> {
        match value.to_ascii_lowercase().as_str() {
            "none" | "0" | "off" => Ok(Self::None),
            "basic" | "1" => Ok(Self::Basic),
            "standard" | "2" | "speed" => Ok(Self::Standard),
            "aggressive" | "3" | "max" => Ok(Self::Aggressive),
            _ => Err(format!(
                "unknown optimization level '{}'; expected one of: none, basic, standard, aggressive",
                value
            )),
        }
    }

    pub fn as_str(self) -> &'static str {
        match self {
            Self::None => "none",
            Self::Basic => "basic",
            Self::Standard => "standard",
            Self::Aggressive => "aggressive",
        }
    }

    pub fn build_mode(self) -> BuildMode {
        match self {
            Self::None => BuildMode::Debug,
            Self::Basic | Self::Standard | Self::Aggressive => BuildMode::Release,
        }
    }

    pub fn enables_layout_optimize(self) -> bool {
        matches!(self, Self::Aggressive)
    }

    pub fn default_for_native_executable() -> Self {
        Self::Aggressive
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OptimizationInventoryEntry {
    pub stage: &'static str,
    pub name: &'static str,
    pub level: NativeOptimizationLevel,
    pub enabled_by_default_for_native_executable: bool,
    pub description: &'static str,
}

const INVENTORY: &[OptimizationInventoryEntry] = &[
    OptimizationInventoryEntry {
        stage: "syntax",
        name: "async desugar",
        level: NativeOptimizationLevel::Basic,
        enabled_by_default_for_native_executable: false,
        description: "Frontend normalization: async/await lowered into state-machine-oriented forms.",
    },
    OptimizationInventoryEntry {
        stage: "syntax",
        name: "placeholder lambda rewrite",
        level: NativeOptimizationLevel::Basic,
        enabled_by_default_for_native_executable: false,
        description: "Frontend normalization: placeholder lambdas rewritten into explicit closures.",
    },
    OptimizationInventoryEntry {
        stage: "syntax",
        name: "collection pattern desugar",
        level: NativeOptimizationLevel::Basic,
        enabled_by_default_for_native_executable: false,
        description: "Frontend normalization: collection update sugar rewritten to simpler operations.",
    },
    OptimizationInventoryEntry {
        stage: "mir",
        name: "constant folding",
        level: NativeOptimizationLevel::Basic,
        enabled_by_default_for_native_executable: false,
        description: "Self-hosted MIR optimization: fold constants and simplify arithmetic identities.",
    },
    OptimizationInventoryEntry {
        stage: "mir",
        name: "copy propagation",
        level: NativeOptimizationLevel::Basic,
        enabled_by_default_for_native_executable: false,
        description: "Self-hosted MIR optimization: propagate copies to expose more cleanup opportunities.",
    },
    OptimizationInventoryEntry {
        stage: "mir",
        name: "dead code elimination",
        level: NativeOptimizationLevel::Basic,
        enabled_by_default_for_native_executable: false,
        description: "Self-hosted MIR optimization: remove unused instructions and dead paths.",
    },
    OptimizationInventoryEntry {
        stage: "mir",
        name: "global value numbering",
        level: NativeOptimizationLevel::Standard,
        enabled_by_default_for_native_executable: false,
        description: "Self-hosted MIR optimization: eliminate redundant computations across basic blocks.",
    },
    OptimizationInventoryEntry {
        stage: "mir",
        name: "common subexpression elimination",
        level: NativeOptimizationLevel::Standard,
        enabled_by_default_for_native_executable: false,
        description: "Self-hosted MIR optimization: remove repeated local computations.",
    },
    OptimizationInventoryEntry {
        stage: "mir",
        name: "inlining and loop pipeline",
        level: NativeOptimizationLevel::Aggressive,
        enabled_by_default_for_native_executable: false,
        description: "Self-hosted MIR optimization: inlining, LICM, loop transforms, outlining, SIMD lowering.",
    },
    OptimizationInventoryEntry {
        stage: "native",
        name: "release build mode",
        level: NativeOptimizationLevel::Basic,
        enabled_by_default_for_native_executable: true,
        description: "Rust native pipeline uses release-mode compiler behavior whenever optimization is enabled.",
    },
    OptimizationInventoryEntry {
        stage: "native",
        name: "4KB layout optimization",
        level: NativeOptimizationLevel::Aggressive,
        enabled_by_default_for_native_executable: true,
        description: "Native linker/code layout optimization for startup and locality-sensitive executables.",
    },
];

pub fn format_optimization_guide() -> String {
    let mut out = String::from(
        "Simple optimization guide\n\
         =========================\n\
         Native executable default profile: aggressive\n\
         Native profile mapping:\n\
           none       -> debug build mode, layout optimization disabled\n\
           basic      -> release build mode, layout optimization disabled\n\
           standard   -> release build mode, layout optimization disabled\n\
           aggressive -> release build mode, layout optimization enabled\n\
         \n\
         Implemented optimization inventory:\n",
    );

    for entry in INVENTORY {
        let native_flag = if entry.enabled_by_default_for_native_executable {
            "native-default"
        } else {
            "inventory-only"
        };
        out.push_str(&format!(
            "  - [{stage}] {name} ({level}, {native_flag})\n    {description}\n",
            stage = entry.stage,
            name = entry.name,
            level = entry.level.as_str(),
            native_flag = native_flag,
            description = entry.description
        ));
    }

    out.push_str(
        "\nNotes:\n\
         - syntax entries refer to grouped frontend desugaring and normalization work\n\
         - mir entries refer to the self-hosted Simple MIR optimization pipeline\n\
         - native entries refer to the Rust native executable build path used by `simple compile --native`\n",
    );

    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_native_optimization_level() {
        assert_eq!(
            NativeOptimizationLevel::parse("none").unwrap(),
            NativeOptimizationLevel::None
        );
        assert_eq!(
            NativeOptimizationLevel::parse("basic").unwrap(),
            NativeOptimizationLevel::Basic
        );
        assert_eq!(
            NativeOptimizationLevel::parse("standard").unwrap(),
            NativeOptimizationLevel::Standard
        );
        assert_eq!(
            NativeOptimizationLevel::parse("aggressive").unwrap(),
            NativeOptimizationLevel::Aggressive
        );
    }

    #[test]
    fn test_default_native_executable_level() {
        assert_eq!(
            NativeOptimizationLevel::default_for_native_executable(),
            NativeOptimizationLevel::Aggressive
        );
    }

    #[test]
    fn test_aggressive_enables_layout_optimize() {
        assert!(NativeOptimizationLevel::Aggressive.enables_layout_optimize());
        assert!(!NativeOptimizationLevel::Standard.enables_layout_optimize());
    }

    #[test]
    fn test_format_optimization_guide_mentions_native_default() {
        let guide = format_optimization_guide();
        assert!(guide.contains("Native executable default profile: aggressive"));
        assert!(guide.contains("[syntax] async desugar"));
        assert!(guide.contains("[native] 4KB layout optimization"));
    }
}
