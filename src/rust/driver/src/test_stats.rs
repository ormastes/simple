//! Statistical analysis for test timing data.
//!
//! Provides functions for:
//! - Computing timing statistics (mean, median, std_dev, percentiles)
//! - Detecting outliers (MAD, IQR, Z-score methods)
//! - Variance analysis (CV%)

use std::collections::HashMap;

/// Statistical summary of test timing data
#[derive(Debug, Clone)]
pub struct TimingStats {
    /// Arithmetic mean (average)
    pub mean: f64,
    /// Median (50th percentile) - more robust than mean
    pub median: f64,
    /// Standard deviation
    pub std_dev: f64,
    /// Coefficient of variation percentage (std_dev/mean × 100)
    pub cv_pct: f64,
    /// Minimum value
    pub min: f64,
    /// Maximum value
    pub max: f64,
    /// Interquartile range (Q3 - Q1)
    pub iqr: f64,
    /// 25th percentile (Q1)
    pub p25: f64,
    /// 50th percentile (median, same as median field)
    pub p50: f64,
    /// 75th percentile (Q3)
    pub p75: f64,
    /// 90th percentile
    pub p90: f64,
    /// 95th percentile
    pub p95: f64,
    /// 99th percentile
    pub p99: f64,
    /// Sample size
    pub count: usize,
}

/// Outlier detection result
#[derive(Debug, Clone)]
pub struct OutlierResult {
    /// Values that are not outliers
    pub inliers: Vec<f64>,
    /// Values that are outliers
    pub outliers: Vec<f64>,
    /// Indices of outliers in original data
    pub outlier_indices: Vec<usize>,
}

/// Outlier detection method
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OutlierMethod {
    /// Interquartile Range method
    IQR,
    /// Median Absolute Deviation method (most robust)
    MAD,
    /// Z-score method (assumes normal distribution)
    ZScore,
}

/// Compute comprehensive statistics from a sample of values
pub fn compute_statistics(samples: &[f64]) -> TimingStats {
    if samples.is_empty() {
        return TimingStats {
            mean: 0.0,
            median: 0.0,
            std_dev: 0.0,
            cv_pct: 0.0,
            min: 0.0,
            max: 0.0,
            iqr: 0.0,
            p25: 0.0,
            p50: 0.0,
            p75: 0.0,
            p90: 0.0,
            p95: 0.0,
            p99: 0.0,
            count: 0,
        };
    }

    let mut sorted = samples.to_vec();
    sorted.sort_by(|a, b| a.partial_cmp(b).unwrap());

    let count = sorted.len();
    let mean = sorted.iter().sum::<f64>() / count as f64;
    let median = percentile(&sorted, 0.5);

    // Compute variance and standard deviation
    let variance = sorted.iter()
        .map(|x| (x - mean).powi(2))
        .sum::<f64>() / count as f64;
    let std_dev = variance.sqrt();

    let cv_pct = if mean != 0.0 {
        (std_dev / mean) * 100.0
    } else {
        0.0
    };

    let p25 = percentile(&sorted, 0.25);
    let p50 = median;
    let p75 = percentile(&sorted, 0.75);
    let p90 = percentile(&sorted, 0.90);
    let p95 = percentile(&sorted, 0.95);
    let p99 = percentile(&sorted, 0.99);

    let iqr = p75 - p25;
    let min = sorted[0];
    let max = sorted[count - 1];

    TimingStats {
        mean,
        median,
        std_dev,
        cv_pct,
        min,
        max,
        iqr,
        p25,
        p50,
        p75,
        p90,
        p95,
        p99,
        count,
    }
}

/// Calculate percentile using linear interpolation
fn percentile(sorted_data: &[f64], p: f64) -> f64 {
    if sorted_data.is_empty() {
        return 0.0;
    }
    if sorted_data.len() == 1 {
        return sorted_data[0];
    }

    let rank = p * (sorted_data.len() - 1) as f64;
    let lower_idx = rank.floor() as usize;
    let upper_idx = rank.ceil() as usize;
    let fraction = rank - lower_idx as f64;

    if lower_idx == upper_idx {
        sorted_data[lower_idx]
    } else {
        sorted_data[lower_idx] * (1.0 - fraction) + sorted_data[upper_idx] * fraction
    }
}

/// Detect outliers using IQR (Interquartile Range) method
///
/// Outliers are values outside [Q1 - 1.5×IQR, Q3 + 1.5×IQR]
pub fn detect_outliers_iqr(samples: &[f64]) -> OutlierResult {
    if samples.len() < 4 {
        // Not enough data for meaningful outlier detection
        return OutlierResult {
            inliers: samples.to_vec(),
            outliers: vec![],
            outlier_indices: vec![],
        };
    }

    let mut sorted = samples.to_vec();
    sorted.sort_by(|a, b| a.partial_cmp(b).unwrap());

    let q1 = percentile(&sorted, 0.25);
    let q3 = percentile(&sorted, 0.75);
    let iqr = q3 - q1;

    let lower_bound = q1 - 1.5 * iqr;
    let upper_bound = q3 + 1.5 * iqr;

    let mut inliers = Vec::new();
    let mut outliers = Vec::new();
    let mut outlier_indices = Vec::new();

    for (i, &value) in samples.iter().enumerate() {
        if value < lower_bound || value > upper_bound {
            outliers.push(value);
            outlier_indices.push(i);
        } else {
            inliers.push(value);
        }
    }

    OutlierResult {
        inliers,
        outliers,
        outlier_indices,
    }
}

/// Detect outliers using MAD (Median Absolute Deviation) method
///
/// Most robust outlier detection method, recommended for response time analysis.
/// Outliers are values where |modified Z-score| > 3.5
pub fn detect_outliers_mad(samples: &[f64]) -> OutlierResult {
    if samples.len() < 3 {
        return OutlierResult {
            inliers: samples.to_vec(),
            outliers: vec![],
            outlier_indices: vec![],
        };
    }

    let mut sorted = samples.to_vec();
    sorted.sort_by(|a, b| a.partial_cmp(b).unwrap());

    let median = percentile(&sorted, 0.5);

    // Compute absolute deviations from median
    let mut deviations: Vec<f64> = samples.iter()
        .map(|&x| (x - median).abs())
        .collect();
    deviations.sort_by(|a, b| a.partial_cmp(b).unwrap());

    let mad = percentile(&deviations, 0.5);

    // Modified Z-score = 0.6745 * (x - median) / MAD
    // Threshold: |modified Z-score| > 3.5
    let threshold = 3.5;
    let mad_normalized = if mad > 0.0 { mad } else { 1e-10 }; // Avoid division by zero

    let mut inliers = Vec::new();
    let mut outliers = Vec::new();
    let mut outlier_indices = Vec::new();

    for (i, &value) in samples.iter().enumerate() {
        let modified_z = 0.6745 * (value - median).abs() / mad_normalized;
        if modified_z > threshold {
            outliers.push(value);
            outlier_indices.push(i);
        } else {
            inliers.push(value);
        }
    }

    OutlierResult {
        inliers,
        outliers,
        outlier_indices,
    }
}

/// Detect outliers using Z-score method
///
/// Assumes normal distribution. Outliers are values where |Z-score| > 3.0
/// Less robust than MAD for skewed distributions.
pub fn detect_outliers_zscore(samples: &[f64]) -> OutlierResult {
    if samples.len() < 3 {
        return OutlierResult {
            inliers: samples.to_vec(),
            outliers: vec![],
            outlier_indices: vec![],
        };
    }

    let stats = compute_statistics(samples);
    let threshold = 3.0;

    let mut inliers = Vec::new();
    let mut outliers = Vec::new();
    let mut outlier_indices = Vec::new();

    for (i, &value) in samples.iter().enumerate() {
        let z_score = if stats.std_dev > 0.0 {
            (value - stats.mean).abs() / stats.std_dev
        } else {
            0.0
        };

        if z_score > threshold {
            outliers.push(value);
            outlier_indices.push(i);
        } else {
            inliers.push(value);
        }
    }

    OutlierResult {
        inliers,
        outliers,
        outlier_indices,
    }
}

/// Detect outliers using specified method
pub fn detect_outliers(samples: &[f64], method: OutlierMethod) -> OutlierResult {
    match method {
        OutlierMethod::IQR => detect_outliers_iqr(samples),
        OutlierMethod::MAD => detect_outliers_mad(samples),
        OutlierMethod::ZScore => detect_outliers_zscore(samples),
    }
}

/// Check if timing has regressed beyond threshold
///
/// Returns true if new_value is significantly worse than baseline
pub fn has_regression(
    new_value: f64,
    baseline_mean: f64,
    baseline_std_dev: f64,
    std_dev_threshold: f64,
) -> bool {
    if baseline_std_dev <= 0.0 {
        return false;
    }

    let z_score = (new_value - baseline_mean) / baseline_std_dev;
    z_score > std_dev_threshold
}

/// Check if timing has changed significantly (for baseline updates)
///
/// Returns true if change exceeds percentage threshold
pub fn has_significant_change(
    new_value: f64,
    baseline_value: f64,
    threshold_pct: f64,
) -> bool {
    if baseline_value == 0.0 {
        return new_value != 0.0;
    }

    let change_pct = ((new_value - baseline_value).abs() / baseline_value) * 100.0;
    change_pct >= threshold_pct
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_compute_statistics_basic() {
        let samples = vec![1.0, 2.0, 3.0, 4.0, 5.0];
        let stats = compute_statistics(&samples);

        assert_eq!(stats.mean, 3.0);
        assert_eq!(stats.median, 3.0);
        assert_eq!(stats.min, 1.0);
        assert_eq!(stats.max, 5.0);
        assert_eq!(stats.count, 5);
    }

    #[test]
    fn test_compute_statistics_empty() {
        let samples: Vec<f64> = vec![];
        let stats = compute_statistics(&samples);

        assert_eq!(stats.mean, 0.0);
        assert_eq!(stats.count, 0);
    }

    #[test]
    fn test_percentile() {
        let samples = vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0];
        let mut sorted = samples.clone();
        sorted.sort_by(|a, b| a.partial_cmp(b).unwrap());

        assert_eq!(percentile(&sorted, 0.5), 5.5); // median
        assert_eq!(percentile(&sorted, 0.25), 3.25); // Q1
        assert_eq!(percentile(&sorted, 0.75), 7.75); // Q3
    }

    #[test]
    fn test_detect_outliers_iqr() {
        let samples = vec![1.0, 2.0, 3.0, 4.0, 5.0, 100.0]; // 100.0 is outlier
        let result = detect_outliers_iqr(&samples);

        assert_eq!(result.inliers.len(), 5);
        assert_eq!(result.outliers.len(), 1);
        assert_eq!(result.outliers[0], 100.0);
    }

    #[test]
    fn test_detect_outliers_mad() {
        let samples = vec![45.0, 46.0, 47.0, 48.0, 49.0, 200.0]; // 200.0 is outlier
        let result = detect_outliers_mad(&samples);

        assert!(result.outliers.len() > 0);
        assert!(result.outliers.contains(&200.0));
    }

    #[test]
    fn test_detect_outliers_zscore() {
        // Z-score method requires more data points to avoid masking effect
        // where a single outlier skews the mean and std_dev
        let samples = vec![
            10.0, 10.0, 10.0, 10.0, 10.0,
            10.0, 10.0, 10.0, 10.0, 10.0,
            200.0,  // outlier - z-score will be >3.0 with this dataset
        ];
        let result = detect_outliers_zscore(&samples);

        assert!(result.outliers.len() > 0, "Expected at least one outlier to be detected");
        assert!(result.outliers.contains(&200.0), "Expected 200.0 to be detected as outlier");
    }

    #[test]
    fn test_has_regression() {
        // New value is 5 std_dev above mean -> regression
        assert!(has_regression(100.0, 50.0, 10.0, 4.0));

        // New value is 2 std_dev above mean -> no regression (threshold is 4)
        assert!(!has_regression(70.0, 50.0, 10.0, 4.0));

        // New value is faster -> no regression
        assert!(!has_regression(40.0, 50.0, 10.0, 4.0));
    }

    #[test]
    fn test_has_significant_change() {
        // 10% change with 5% threshold -> significant
        assert!(has_significant_change(110.0, 100.0, 5.0));

        // 3% change with 5% threshold -> not significant
        assert!(!has_significant_change(103.0, 100.0, 5.0));

        // Improvement also counts as change
        assert!(has_significant_change(90.0, 100.0, 5.0));
    }

    #[test]
    fn test_cv_percentage() {
        let samples = vec![100.0, 110.0, 90.0, 105.0, 95.0];
        let stats = compute_statistics(&samples);

        // CV% should be around 7-8%
        assert!(stats.cv_pct > 5.0 && stats.cv_pct < 10.0);
    }
}
