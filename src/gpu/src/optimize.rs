//! GPU Optimization Analysis
//!
//! This module provides tools for analyzing and optimizing GPU kernel code,
//! including divergence analysis and memory access pattern optimization.

use std::collections::HashMap;

/// Analysis result for control flow divergence.
#[derive(Debug, Clone)]
pub struct DivergenceAnalysis {
    /// Branches that may cause thread divergence.
    pub divergent_branches: Vec<DivergentBranch>,
    /// Overall divergence score (0.0 = no divergence, 1.0 = maximum divergence).
    pub divergence_score: f64,
    /// Recommendations for reducing divergence.
    pub recommendations: Vec<String>,
}

impl DivergenceAnalysis {
    /// Create a new analysis with no divergence.
    pub fn none() -> Self {
        DivergenceAnalysis {
            divergent_branches: Vec::new(),
            divergence_score: 0.0,
            recommendations: Vec::new(),
        }
    }

    /// Check if the analysis found any divergence.
    pub fn has_divergence(&self) -> bool {
        !self.divergent_branches.is_empty()
    }
}

/// A potentially divergent branch in a kernel.
#[derive(Debug, Clone)]
pub struct DivergentBranch {
    /// Location in source (line number or offset).
    pub location: usize,
    /// Description of the branch condition.
    pub condition: String,
    /// Estimated divergence probability (0.0 to 1.0).
    pub probability: f64,
    /// Suggested fix if available.
    pub suggestion: Option<String>,
}

/// Analyze a kernel for control flow divergence.
///
/// Divergence occurs when threads in the same warp take different branches,
/// causing serialization of execution.
pub fn analyze_divergence(kernel_source: &str) -> DivergenceAnalysis {
    let mut branches = Vec::new();
    let mut recommendations = Vec::new();

    // Simple heuristic analysis based on patterns
    let lines: Vec<&str> = kernel_source.lines().collect();

    for (i, line) in lines.iter().enumerate() {
        let line = line.trim();

        // Check for thread-dependent conditionals
        if line.contains("if") && contains_thread_dependent(line) {
            let probability = estimate_divergence_probability(line);

            branches.push(DivergentBranch {
                location: i + 1,
                condition: line.to_string(),
                probability,
                suggestion: suggest_divergence_fix(line),
            });
        }

        // Check for potentially divergent loops
        if (line.contains("while") || line.contains("for")) && contains_thread_dependent(line) {
            branches.push(DivergentBranch {
                location: i + 1,
                condition: line.to_string(),
                probability: 0.5, // Loops are often more problematic
                suggestion: Some("Consider using predicated execution or restructuring the loop".to_string()),
            });
        }
    }

    // Calculate overall divergence score
    let divergence_score = if branches.is_empty() {
        0.0
    } else {
        branches.iter().map(|b| b.probability).sum::<f64>() / branches.len() as f64
    };

    // Generate recommendations
    if !branches.is_empty() {
        recommendations.push("Consider using predicated execution for simple conditionals".to_string());
        recommendations.push("Restructure data to minimize thread-dependent branches".to_string());
        recommendations.push("Use warp-uniform control flow where possible".to_string());
    }

    DivergenceAnalysis {
        divergent_branches: branches,
        divergence_score,
        recommendations,
    }
}

/// Check if a line contains thread-dependent expressions.
fn contains_thread_dependent(line: &str) -> bool {
    let thread_vars = [
        "global_id",
        "local_id",
        "thread_id",
        "lane_id",
        "idx",
        "[i]",
        "[j]",
        "[k]",
    ];

    thread_vars.iter().any(|var| line.contains(var))
}

/// Estimate divergence probability based on the condition.
fn estimate_divergence_probability(condition: &str) -> f64 {
    // Boundary checks usually have low divergence
    if condition.contains("< len") || condition.contains(">= 0") || condition.contains("< size") {
        return 0.1;
    }

    // Modulo operations often cause divergence
    if condition.contains("%") {
        return 0.7;
    }

    // Comparisons with thread ID have medium divergence
    if condition.contains("global_id") || condition.contains("local_id") {
        return 0.5;
    }

    0.3 // Default medium-low probability
}

/// Suggest a fix for divergent code.
fn suggest_divergence_fix(condition: &str) -> Option<String> {
    if condition.contains("%") {
        return Some("Consider restructuring to avoid modulo-based branching".to_string());
    }

    if condition.contains("global_id") {
        return Some("Use predication or data restructuring to avoid thread-dependent branches".to_string());
    }

    None
}

/// Memory access pattern analysis.
#[derive(Debug, Clone)]
pub struct MemoryAnalysis {
    /// Memory access patterns detected.
    pub access_patterns: Vec<AccessPattern>,
    /// Bank conflict analysis.
    pub bank_conflicts: Vec<BankConflict>,
    /// Coalescing efficiency (0.0 to 1.0).
    pub coalescing_efficiency: f64,
    /// Recommendations for memory optimization.
    pub recommendations: Vec<String>,
}

impl MemoryAnalysis {
    /// Create an analysis with optimal memory access.
    pub fn optimal() -> Self {
        MemoryAnalysis {
            access_patterns: Vec::new(),
            bank_conflicts: Vec::new(),
            coalescing_efficiency: 1.0,
            recommendations: Vec::new(),
        }
    }

    /// Check if memory access is efficient.
    pub fn is_efficient(&self) -> bool {
        self.bank_conflicts.is_empty() && self.coalescing_efficiency > 0.8
    }
}

/// A memory access pattern.
#[derive(Debug, Clone)]
pub struct AccessPattern {
    /// Type of access pattern.
    pub pattern_type: AccessPatternType,
    /// Location in source.
    pub location: usize,
    /// Description.
    pub description: String,
}

/// Types of memory access patterns.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AccessPatternType {
    /// Sequential/coalesced access (optimal).
    Sequential,
    /// Strided access (may reduce bandwidth).
    Strided,
    /// Random access (worst case).
    Random,
    /// Broadcast (same address for all threads).
    Broadcast,
}

impl AccessPatternType {
    /// Get the efficiency rating for this pattern.
    pub fn efficiency(&self) -> f64 {
        match self {
            AccessPatternType::Sequential => 1.0,
            AccessPatternType::Broadcast => 0.9, // Broadcast is efficient for reads
            AccessPatternType::Strided => 0.5,
            AccessPatternType::Random => 0.1,
        }
    }
}

/// A potential bank conflict.
#[derive(Debug, Clone)]
pub struct BankConflict {
    /// Location in source.
    pub location: usize,
    /// Number of banks involved.
    pub num_banks: u32,
    /// Degree of conflict (how many threads conflict).
    pub conflict_degree: u32,
    /// Description.
    pub description: String,
    /// Suggested fix.
    pub suggestion: String,
}

/// Configuration for memory analysis.
#[derive(Debug, Clone)]
pub struct MemoryAnalysisConfig {
    /// Number of memory banks (typically 32).
    pub num_banks: u32,
    /// Bank width in bytes (typically 4).
    pub bank_width: u32,
    /// Warp size for coalescing analysis.
    pub warp_size: u32,
    /// Cache line size in bytes.
    pub cache_line_size: u32,
}

impl Default for MemoryAnalysisConfig {
    fn default() -> Self {
        MemoryAnalysisConfig {
            num_banks: 32,
            bank_width: 4,
            warp_size: 32,
            cache_line_size: 128,
        }
    }
}

/// Analyze memory access patterns in a kernel.
pub fn analyze_memory_access(
    kernel_source: &str,
    config: &MemoryAnalysisConfig,
) -> MemoryAnalysis {
    let mut patterns = Vec::new();
    let mut bank_conflicts = Vec::new();
    let mut recommendations = Vec::new();

    let lines: Vec<&str> = kernel_source.lines().collect();

    for (i, line) in lines.iter().enumerate() {
        let line = line.trim();

        // Check for shared memory access patterns
        if line.contains("shared") || line.contains("local") {
            if let Some(pattern) = detect_access_pattern(line, i + 1) {
                patterns.push(pattern);
            }

            if let Some(conflict) = detect_bank_conflict(line, i + 1, config) {
                bank_conflicts.push(conflict);
            }
        }

        // Check for global memory access
        if line.contains("[") && !line.contains("shared") && !line.contains("local") {
            if let Some(pattern) = detect_access_pattern(line, i + 1) {
                patterns.push(pattern);
            }
        }
    }

    // Calculate coalescing efficiency
    let coalescing_efficiency = if patterns.is_empty() {
        1.0
    } else {
        patterns.iter().map(|p| p.pattern_type.efficiency()).sum::<f64>() / patterns.len() as f64
    };

    // Generate recommendations
    if !bank_conflicts.is_empty() {
        recommendations.push("Add padding to shared memory arrays to avoid bank conflicts".to_string());
    }
    if coalescing_efficiency < 0.8 {
        recommendations.push("Restructure memory access to be more sequential".to_string());
        recommendations.push("Consider using shared memory for non-coalesced global access".to_string());
    }

    MemoryAnalysis {
        access_patterns: patterns,
        bank_conflicts,
        coalescing_efficiency,
        recommendations,
    }
}

/// Detect the access pattern in a line of code.
fn detect_access_pattern(line: &str, location: usize) -> Option<AccessPattern> {
    // Check for sequential access (arr[global_id])
    if line.contains("[global_id]") || line.contains("[idx]") || line.contains("[i]") {
        return Some(AccessPattern {
            pattern_type: AccessPatternType::Sequential,
            location,
            description: "Sequential/coalesced access".to_string(),
        });
    }

    // Check for strided access (arr[global_id * stride])
    if line.contains("*") && (line.contains("[") && line.contains("]")) {
        return Some(AccessPattern {
            pattern_type: AccessPatternType::Strided,
            location,
            description: "Strided access pattern detected".to_string(),
        });
    }

    // Check for broadcast (same index for all threads)
    if line.contains("[0]") || line.contains("[const]") {
        return Some(AccessPattern {
            pattern_type: AccessPatternType::Broadcast,
            location,
            description: "Broadcast read (same data for all threads)".to_string(),
        });
    }

    None
}

/// Detect potential bank conflicts.
fn detect_bank_conflict(
    line: &str,
    location: usize,
    config: &MemoryAnalysisConfig,
) -> Option<BankConflict> {
    // Check for strided shared memory access
    if line.contains("[") && line.contains("*") {
        // Extract stride if possible
        let stride = extract_stride(line);

        if stride > 0 && stride % config.num_banks == 0 {
            return Some(BankConflict {
                location,
                num_banks: config.num_banks,
                conflict_degree: config.num_banks,
                description: format!("Stride {} causes {}-way bank conflict", stride, config.num_banks),
                suggestion: format!("Add {} bytes of padding to the array dimension", config.bank_width),
            });
        }
    }

    // Check for column-major access in row-major layout
    if line.contains("[j][i]") || line.contains("[y][x]") {
        return Some(BankConflict {
            location,
            num_banks: config.num_banks,
            conflict_degree: config.warp_size,
            description: "Column-major access in row-major layout".to_string(),
            suggestion: "Transpose the access pattern or use shared memory".to_string(),
        });
    }

    None
}

/// Extract stride from an access pattern.
fn extract_stride(line: &str) -> u32 {
    // Simple heuristic - look for common stride patterns
    if line.contains("* 32") {
        return 32;
    }
    if line.contains("* 64") {
        return 64;
    }
    if line.contains("* 128") {
        return 128;
    }
    0
}

/// Optimization hints for kernel compilation.
#[derive(Debug, Clone, Default)]
pub struct OptimizationHints {
    /// Suggested work group size.
    pub work_group_size: Option<[u32; 3]>,
    /// Minimum registers per thread.
    pub min_registers: Option<u32>,
    /// Shared memory size hint.
    pub shared_memory_hint: Option<usize>,
    /// Enable fast math optimizations.
    pub fast_math: bool,
    /// Enable loop unrolling.
    pub unroll_loops: bool,
    /// Custom compiler flags.
    pub custom_flags: HashMap<String, String>,
}

impl OptimizationHints {
    /// Create hints optimized for compute-bound kernels.
    pub fn compute_bound() -> Self {
        OptimizationHints {
            work_group_size: Some([256, 1, 1]),
            fast_math: true,
            unroll_loops: true,
            ..Default::default()
        }
    }

    /// Create hints optimized for memory-bound kernels.
    pub fn memory_bound() -> Self {
        OptimizationHints {
            work_group_size: Some([128, 1, 1]), // Smaller for better occupancy
            fast_math: false,
            unroll_loops: false,
            ..Default::default()
        }
    }

    /// Create hints optimized for reduction operations.
    pub fn reduction() -> Self {
        OptimizationHints {
            work_group_size: Some([256, 1, 1]),
            shared_memory_hint: Some(256 * 4), // For local reduction
            fast_math: true,
            unroll_loops: true,
            ..Default::default()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_divergence_analysis_no_divergence() {
        let source = r#"
            let idx = global_id()
            output[idx] = input[idx] * 2.0
        "#;

        let analysis = analyze_divergence(source);
        assert!(!analysis.has_divergence());
        assert_eq!(analysis.divergence_score, 0.0);
    }

    #[test]
    fn test_divergence_analysis_with_branch() {
        let source = r#"
            let idx = global_id()
            if idx % 2 == 0:
                output[idx] = input[idx] * 2.0
            else:
                output[idx] = input[idx] * 3.0
        "#;

        let analysis = analyze_divergence(source);
        assert!(analysis.has_divergence());
        assert!(analysis.divergence_score > 0.0);
    }

    #[test]
    fn test_memory_analysis_sequential() {
        let source = r#"
            let idx = global_id()
            output[idx] = input[idx] * 2.0
        "#;

        let config = MemoryAnalysisConfig::default();
        let analysis = analyze_memory_access(source, &config);

        assert!(analysis.is_efficient());
    }

    #[test]
    fn test_bank_conflict_detection() {
        // Test column-major access pattern which causes bank conflicts
        // The line must contain "shared" or "local" AND the access pattern
        let source = r#"
            let val = shared_data[j][i]
        "#;

        let config = MemoryAnalysisConfig::default();
        let analysis = analyze_memory_access(source, &config);

        // Column-major access in shared memory causes bank conflicts
        assert!(!analysis.bank_conflicts.is_empty(), "Expected bank conflict for column-major access");
    }

    #[test]
    fn test_optimization_hints() {
        let hints = OptimizationHints::compute_bound();
        assert!(hints.fast_math);
        assert!(hints.unroll_loops);

        let hints = OptimizationHints::memory_bound();
        assert!(!hints.fast_math);
        assert!(!hints.unroll_loops);
    }

    #[test]
    fn test_access_pattern_types() {
        assert_eq!(AccessPatternType::Sequential.efficiency(), 1.0);
        assert_eq!(AccessPatternType::Random.efficiency(), 0.1);
    }
}
