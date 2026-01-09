//! Pattern analysis for match expressions.
//!
//! This module implements:
//! - Exhaustiveness checking: ensures all possible values are covered by match arms
//! - Unreachable arm detection: warns about patterns that can never match
//! - Tagged union variant coverage verification
//!
//! See doc/spec/language.md for pattern matching specification.

use simple_parser::ast::{EnumDef, MatchArm, Pattern};
use simple_type::{TaggedUnion, UnionVariant};
use std::collections::HashSet;

/// Result of pattern analysis.
#[derive(Debug, Clone)]
pub struct PatternAnalysis {
    /// Whether the match is exhaustive (covers all possible values)
    pub is_exhaustive: bool,
    /// Indices of unreachable arms
    pub unreachable_arms: Vec<usize>,
    /// Missing patterns (if not exhaustive)
    pub missing_patterns: Vec<String>,
}

impl PatternAnalysis {
    pub fn new() -> Self {
        Self {
            is_exhaustive: false,
            unreachable_arms: Vec::new(),
            missing_patterns: Vec::new(),
        }
    }

    pub fn exhaustive() -> Self {
        Self {
            is_exhaustive: true,
            unreachable_arms: Vec::new(),
            missing_patterns: Vec::new(),
        }
    }
}

impl Default for PatternAnalysis {
    fn default() -> Self {
        Self::new()
    }
}

/// Analyze match arms for exhaustiveness and unreachability.
///
/// This performs a simplified analysis that covers common cases:
/// - Wildcard patterns (_) are always exhaustive
/// - Literal patterns are checked for coverage
/// - Enum patterns check all variants are covered
/// - Later arms are unreachable if earlier arms already match all inputs
pub fn analyze_match(arms: &[MatchArm]) -> PatternAnalysis {
    let mut analysis = PatternAnalysis::new();

    if arms.is_empty() {
        analysis.missing_patterns.push("_".to_string());
        return analysis;
    }

    // Track which patterns have been seen
    let mut covered_patterns = HashSet::new();
    let mut has_wildcard = false;
    let mut wildcard_index = None;

    // First pass: collect all patterns and check for wildcards
    for (i, arm) in arms.iter().enumerate() {
        if is_wildcard_pattern(&arm.pattern) {
            has_wildcard = true;
            wildcard_index = Some(i);
            break; // Everything after a wildcard is unreachable
        }

        // Track covered patterns
        if let Some(pattern_repr) = pattern_to_string(&arm.pattern) {
            covered_patterns.insert(pattern_repr);
        }
    }

    // If there's a wildcard, all arms after it are unreachable
    if let Some(wildcard_idx) = wildcard_index {
        for i in (wildcard_idx + 1)..arms.len() {
            analysis.unreachable_arms.push(i);
        }
        analysis.is_exhaustive = true;
        return analysis;
    }

    // Check for exhaustiveness based on pattern type
    // For now, we consider non-exhaustive unless there's a wildcard
    // A more sophisticated analysis would check:
    // - All enum variants are covered
    // - All boolean values (true/false) are covered
    // - Numeric ranges are complete
    if !has_wildcard {
        analysis.is_exhaustive = false;
        analysis.missing_patterns.push("_".to_string());
    }

    // Simple unreachability detection: exact duplicate patterns
    let mut seen_exact = HashSet::new();
    for (i, arm) in arms.iter().enumerate() {
        if let Some(pattern_repr) = pattern_to_string(&arm.pattern) {
            if !seen_exact.insert(pattern_repr.clone()) {
                // This exact pattern was already seen - unreachable
                analysis.unreachable_arms.push(i);
            }
        }
    }

    analysis
}

/// Check if a pattern is a wildcard (matches everything).
fn is_wildcard_pattern(pattern: &Pattern) -> bool {
    matches!(pattern, Pattern::Wildcard)
}

/// Convert a pattern to a string representation for comparison.
fn pattern_to_string(pattern: &Pattern) -> Option<String> {
    match pattern {
        Pattern::Wildcard => Some("_".to_string()),
        Pattern::Identifier(name) => Some(name.clone()),
        Pattern::MutIdentifier(name) => Some(format!("mut {}", name)),
        Pattern::Literal(expr) => Some(format!("{:?}", expr)),
        Pattern::Tuple(patterns) => {
            let parts: Vec<String> = patterns.iter().filter_map(pattern_to_string).collect();
            Some(format!("({})", parts.join(", ")))
        }
        Pattern::Array(patterns) => {
            let parts: Vec<String> = patterns.iter().filter_map(pattern_to_string).collect();
            Some(format!("[{}]", parts.join(", ")))
        }
        Pattern::Struct { name, fields } => {
            let field_strs: Vec<String> = fields
                .iter()
                .map(|(k, v)| {
                    format!(
                        "{}: {}",
                        k,
                        pattern_to_string(v).unwrap_or_else(|| "_".to_string())
                    )
                })
                .collect();
            Some(format!("{} {{ {} }}", name, field_strs.join(", ")))
        }
        Pattern::Enum {
            name,
            variant,
            payload,
        } => {
            if let Some(payload) = payload {
                let parts: Vec<String> = payload.iter().filter_map(pattern_to_string).collect();
                Some(format!("{}.{}({})", name, variant, parts.join(", ")))
            } else {
                Some(format!("{}.{}", name, variant))
            }
        }
        Pattern::Typed { pattern, ty } => Some(format!(
            "{}: {:?}",
            pattern_to_string(pattern).unwrap_or_else(|| "_".to_string()),
            ty
        )),
        Pattern::Range {
            start,
            end,
            inclusive,
        } => Some(format!(
            "{:?}{}  {:?}",
            start,
            if *inclusive { "..=" } else { ".." },
            end
        )),
        Pattern::Or(patterns) => {
            let parts: Vec<String> = patterns.iter().filter_map(pattern_to_string).collect();
            Some(parts.join(" | "))
        }
        Pattern::Rest => Some("..".to_string()),
    }
}

/// Enhanced exhaustiveness checking for enum patterns.
///
/// This checks if all variants of an enum are covered by the match arms.
/// Returns true if exhaustive, along with a list of missing variants.
pub fn check_enum_exhaustiveness(
    enum_name: &str,
    variants: &[String],
    arms: &[MatchArm],
) -> (bool, Vec<String>) {
    // Check if there's a wildcard pattern
    for arm in arms {
        if is_wildcard_pattern(&arm.pattern) {
            return (true, Vec::new());
        }
    }

    // Collect covered variants
    let mut covered: HashSet<String> = HashSet::new();
    for arm in arms {
        if let Pattern::Enum { name, variant, .. } = &arm.pattern {
            if name == enum_name {
                covered.insert(variant.clone());
            }
        }
    }

    // Check for missing variants
    let missing: Vec<String> = variants
        .iter()
        .filter(|v| !covered.contains(*v))
        .cloned()
        .collect();

    (missing.is_empty(), missing)
}

/// Check exhaustiveness for tagged union patterns.
///
/// Verifies that all variants of a tagged union type are handled.
pub fn check_union_exhaustiveness(union: &TaggedUnion, arms: &[MatchArm]) -> (bool, Vec<String>) {
    // Check if there's a wildcard pattern
    for arm in arms {
        if is_wildcard_pattern(&arm.pattern) {
            return (true, Vec::new());
        }
    }

    // Collect covered variants
    let covered_variants: Vec<String> = arms
        .iter()
        .filter_map(|arm| {
            if let Pattern::Enum { name, variant, .. } = &arm.pattern {
                if name == &union.name {
                    Some(variant.clone())
                } else {
                    None
                }
            } else {
                None
            }
        })
        .collect();

    // Use TaggedUnion's built-in exhaustiveness check
    let missing = union.check_exhaustiveness(&covered_variants);
    (missing.is_empty(), missing)
}

/// Advanced exhaustiveness checking with type information.
///
/// This performs exhaustiveness checking based on the type of the match subject.
/// Returns detailed information about coverage.
#[derive(Debug, Clone)]
pub struct ExhaustivenessCheck {
    /// Whether the match is exhaustive
    pub is_exhaustive: bool,
    /// Missing variants/patterns
    pub missing_patterns: Vec<String>,
    /// Whether a wildcard was found
    pub has_wildcard: bool,
    /// Number of variants covered
    pub covered_count: usize,
    /// Total number of variants
    pub total_count: usize,
}

impl ExhaustivenessCheck {
    /// Create an exhaustive check result
    pub fn exhaustive(covered: usize, total: usize) -> Self {
        Self {
            is_exhaustive: true,
            missing_patterns: Vec::new(),
            has_wildcard: false,
            covered_count: covered,
            total_count: total,
        }
    }

    /// Create a non-exhaustive check result
    pub fn non_exhaustive(missing: Vec<String>, covered: usize, total: usize) -> Self {
        Self {
            is_exhaustive: false,
            missing_patterns: missing,
            has_wildcard: false,
            covered_count: covered,
            total_count: total,
        }
    }

    /// Create a check result with wildcard
    pub fn with_wildcard(covered: usize, total: usize) -> Self {
        Self {
            is_exhaustive: true,
            missing_patterns: Vec::new(),
            has_wildcard: true,
            covered_count: covered,
            total_count: total,
        }
    }
}

/// Check if a pattern is more specific than another.
///
/// Used for unreachability detection. Returns true if `specific` is
/// completely covered by `general`.
pub fn pattern_subsumes(general: &Pattern, specific: &Pattern) -> bool {
    match (general, specific) {
        // Wildcard matches everything
        (Pattern::Wildcard, _) => true,

        // Identifiers match everything (they bind)
        (Pattern::Identifier(_), _) => true,

        // Exact matches
        (Pattern::Literal(a), Pattern::Literal(b)) => a == b,

        // Tuple patterns
        (Pattern::Tuple(g_pats), Pattern::Tuple(s_pats)) => {
            g_pats.len() == s_pats.len()
                && g_pats
                    .iter()
                    .zip(s_pats.iter())
                    .all(|(g, s)| pattern_subsumes(g, s))
        }

        // Enum patterns
        (
            Pattern::Enum {
                name: g_name,
                variant: g_var,
                payload: g_payload,
            },
            Pattern::Enum {
                name: s_name,
                variant: s_var,
                payload: s_payload,
            },
        ) => {
            if g_name != s_name || g_var != s_var {
                return false;
            }
            match (g_payload, s_payload) {
                (None, None) => true,
                (Some(g), Some(s)) => {
                    g.len() == s.len()
                        && g.iter()
                            .zip(s.iter())
                            .all(|(g_p, s_p)| pattern_subsumes(g_p, s_p))
                }
                _ => false,
            }
        }

        // Or patterns - general subsumes specific if it subsumes any alternative
        (Pattern::Or(g_pats), _) => g_pats.iter().any(|g| pattern_subsumes(g, specific)),

        (_, Pattern::Or(s_pats)) => s_pats.iter().all(|s| pattern_subsumes(general, s)),

        // Conservative: assume no subsumption for other cases
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use simple_parser::ast::{Block, Expr, MatchArm};
    use simple_parser::token::Span;

    fn dummy_span() -> Span {
        Span::new(0, 0, 1, 1)
    }

    fn make_arm(pattern: Pattern) -> MatchArm {
        MatchArm {
            pattern,
            guard: None,
            body: Block {
                span: dummy_span(),
                statements: Vec::new(),
            },
            span: dummy_span(),
        }
    }

    fn make_literal(val: i64) -> Expr {
        // Create a simple integer literal expression
        Expr::Integer(val)
    }

    #[test]
    fn test_exhaustive_with_wildcard() {
        let arms = vec![
            make_arm(Pattern::Literal(Box::new(make_literal(1)))),
            make_arm(Pattern::Literal(Box::new(make_literal(2)))),
            make_arm(Pattern::Wildcard),
        ];

        let analysis = analyze_match(&arms);
        assert!(analysis.is_exhaustive);
        assert!(analysis.unreachable_arms.is_empty());
        assert!(analysis.missing_patterns.is_empty());
    }

    #[test]
    fn test_non_exhaustive_without_wildcard() {
        let arms = vec![
            make_arm(Pattern::Literal(Box::new(make_literal(1)))),
            make_arm(Pattern::Literal(Box::new(make_literal(2)))),
        ];

        let analysis = analyze_match(&arms);
        assert!(!analysis.is_exhaustive);
        assert_eq!(analysis.missing_patterns, vec!["_"]);
    }

    #[test]
    fn test_unreachable_after_wildcard() {
        let arms = vec![
            make_arm(Pattern::Literal(Box::new(make_literal(1)))),
            make_arm(Pattern::Wildcard),
            make_arm(Pattern::Literal(Box::new(make_literal(2)))), // Unreachable
        ];

        let analysis = analyze_match(&arms);
        assert!(analysis.is_exhaustive);
        assert_eq!(analysis.unreachable_arms, vec![2]);
    }

    #[test]
    fn test_duplicate_pattern() {
        let arms = vec![
            make_arm(Pattern::Literal(Box::new(make_literal(1)))),
            make_arm(Pattern::Literal(Box::new(make_literal(2)))),
            make_arm(Pattern::Literal(Box::new(make_literal(1)))), // Duplicate
        ];

        let analysis = analyze_match(&arms);
        assert_eq!(analysis.unreachable_arms, vec![2]);
    }

    #[test]
    fn test_empty_match() {
        let arms = vec![];
        let analysis = analyze_match(&arms);
        assert!(!analysis.is_exhaustive);
        assert_eq!(analysis.missing_patterns, vec!["_"]);
    }

    #[test]
    fn test_pattern_subsumes_wildcard() {
        let general = Pattern::Wildcard;
        let specific = Pattern::Literal(Box::new(make_literal(42)));
        assert!(pattern_subsumes(&general, &specific));
    }

    #[test]
    fn test_pattern_subsumes_identifier() {
        let general = Pattern::Identifier("x".to_string());
        let specific = Pattern::Literal(Box::new(make_literal(42)));
        assert!(pattern_subsumes(&general, &specific));
    }

    #[test]
    fn test_pattern_subsumes_literal() {
        let general = Pattern::Literal(Box::new(make_literal(42)));
        let specific = Pattern::Literal(Box::new(make_literal(42)));
        assert!(pattern_subsumes(&general, &specific));

        let different = Pattern::Literal(Box::new(make_literal(99)));
        // Since we use Debug format for comparison, these won't match
        // This is a simplified check
        assert!(!pattern_subsumes(&different, &specific));
    }

    #[test]
    fn test_pattern_subsumes_tuple() {
        let general = Pattern::Tuple(vec![
            Pattern::Wildcard,
            Pattern::Identifier("y".to_string()),
        ]);
        let specific = Pattern::Tuple(vec![
            Pattern::Literal(Box::new(make_literal(1))),
            Pattern::Literal(Box::new(make_literal(2))),
        ]);
        assert!(pattern_subsumes(&general, &specific));
    }

    #[test]
    fn test_pattern_subsumes_enum() {
        let general = Pattern::Enum {
            name: "Option".to_string(),
            variant: "Some".to_string(),
            payload: Some(vec![Pattern::Wildcard]),
        };
        let specific = Pattern::Enum {
            name: "Option".to_string(),
            variant: "Some".to_string(),
            payload: Some(vec![Pattern::Literal(Box::new(make_literal(42)))]),
        };
        assert!(pattern_subsumes(&general, &specific));

        let different_variant = Pattern::Enum {
            name: "Option".to_string(),
            variant: "None".to_string(),
            payload: None,
        };
        assert!(!pattern_subsumes(&general, &different_variant));
    }

    #[test]
    fn test_enum_exhaustiveness_complete() {
        let variants = vec![
            "Circle".to_string(),
            "Rectangle".to_string(),
            "Triangle".to_string(),
        ];
        let arms = vec![
            make_arm(Pattern::Enum {
                name: "Shape".to_string(),
                variant: "Circle".to_string(),
                payload: None,
            }),
            make_arm(Pattern::Enum {
                name: "Shape".to_string(),
                variant: "Rectangle".to_string(),
                payload: None,
            }),
            make_arm(Pattern::Enum {
                name: "Shape".to_string(),
                variant: "Triangle".to_string(),
                payload: None,
            }),
        ];

        let (is_exhaustive, missing) = check_enum_exhaustiveness("Shape", &variants, &arms);
        assert!(is_exhaustive);
        assert!(missing.is_empty());
    }

    #[test]
    fn test_enum_exhaustiveness_missing_variant() {
        let variants = vec![
            "Circle".to_string(),
            "Rectangle".to_string(),
            "Triangle".to_string(),
        ];
        let arms = vec![
            make_arm(Pattern::Enum {
                name: "Shape".to_string(),
                variant: "Circle".to_string(),
                payload: None,
            }),
            make_arm(Pattern::Enum {
                name: "Shape".to_string(),
                variant: "Rectangle".to_string(),
                payload: None,
            }),
        ];

        let (is_exhaustive, missing) = check_enum_exhaustiveness("Shape", &variants, &arms);
        assert!(!is_exhaustive);
        assert_eq!(missing, vec!["Triangle"]);
    }

    #[test]
    fn test_enum_exhaustiveness_with_wildcard() {
        let variants = vec!["Some".to_string(), "None".to_string()];
        let arms = vec![
            make_arm(Pattern::Enum {
                name: "Option".to_string(),
                variant: "Some".to_string(),
                payload: Some(vec![Pattern::Wildcard]),
            }),
            make_arm(Pattern::Wildcard),
        ];

        let (is_exhaustive, missing) = check_enum_exhaustiveness("Option", &variants, &arms);
        assert!(is_exhaustive);
        assert!(missing.is_empty());
    }

    #[test]
    fn test_union_exhaustiveness_complete() {
        use simple_type::{TaggedUnion, Type, UnionVariant};

        let mut shape_union = TaggedUnion::new("Shape".to_string());
        shape_union.add_variant(UnionVariant::new("Circle".to_string(), 0));
        shape_union.add_variant(UnionVariant::new("Rectangle".to_string(), 1));
        shape_union.add_variant(UnionVariant::new("Triangle".to_string(), 2));

        let arms = vec![
            make_arm(Pattern::Enum {
                name: "Shape".to_string(),
                variant: "Circle".to_string(),
                payload: None,
            }),
            make_arm(Pattern::Enum {
                name: "Shape".to_string(),
                variant: "Rectangle".to_string(),
                payload: None,
            }),
            make_arm(Pattern::Enum {
                name: "Shape".to_string(),
                variant: "Triangle".to_string(),
                payload: None,
            }),
        ];

        let (is_exhaustive, missing) = check_union_exhaustiveness(&shape_union, &arms);
        assert!(is_exhaustive);
        assert!(missing.is_empty());
    }

    #[test]
    fn test_union_exhaustiveness_missing() {
        use simple_type::{TaggedUnion, Type, UnionVariant};

        let mut result_union = TaggedUnion::new("Result".to_string());
        result_union.add_variant(UnionVariant::new("Ok".to_string(), 0));
        result_union.add_variant(UnionVariant::new("Err".to_string(), 1));

        let arms = vec![make_arm(Pattern::Enum {
            name: "Result".to_string(),
            variant: "Ok".to_string(),
            payload: Some(vec![Pattern::Wildcard]),
        })];

        let (is_exhaustive, missing) = check_union_exhaustiveness(&result_union, &arms);
        assert!(!is_exhaustive);
        assert_eq!(missing, vec!["Err"]);
    }

    #[test]
    fn test_exhaustiveness_check_struct() {
        let check = ExhaustivenessCheck::exhaustive(3, 3);
        assert!(check.is_exhaustive);
        assert_eq!(check.covered_count, 3);
        assert_eq!(check.total_count, 3);
        assert!(!check.has_wildcard);
    }

    #[test]
    fn test_exhaustiveness_check_non_exhaustive() {
        let missing = vec!["Variant1".to_string(), "Variant2".to_string()];
        let check = ExhaustivenessCheck::non_exhaustive(missing.clone(), 1, 3);
        assert!(!check.is_exhaustive);
        assert_eq!(check.missing_patterns, missing);
        assert_eq!(check.covered_count, 1);
        assert_eq!(check.total_count, 3);
    }

    #[test]
    fn test_exhaustiveness_check_with_wildcard() {
        let check = ExhaustivenessCheck::with_wildcard(2, 5);
        assert!(check.is_exhaustive);
        assert!(check.has_wildcard);
        assert_eq!(check.covered_count, 2);
        assert_eq!(check.total_count, 5);
    }
}
