//! Coverage metrics implementation

use serde::{Deserialize, Serialize};

/// Line/branch coverage metrics
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct CoverageMetrics {
    pub total: usize,
    pub covered: usize,
    pub percent: f64,
}

impl CoverageMetrics {
    pub fn new(total: usize, covered: usize) -> Self {
        let percent = if total == 0 {
            100.0
        } else {
            (covered as f64 / total as f64) * 100.0
        };
        Self {
            total,
            covered,
            percent,
        }
    }

    pub fn add(&mut self, other: &CoverageMetrics) {
        self.total += other.total;
        self.covered += other.covered;
        self.percent = if self.total == 0 {
            100.0
        } else {
            (self.covered as f64 / self.total as f64) * 100.0
        };
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_coverage_metrics() {
        let metrics = CoverageMetrics::new(10, 8);
        assert_eq!(metrics.total, 10);
        assert_eq!(metrics.covered, 8);
        assert!((metrics.percent - 80.0).abs() < 0.01);
    }
}
