//! Test run record types — TestRunStatus, TestRunRecord, validation, Record impl.

use crate::unified_db::Record;
use serde::{Deserialize, Serialize};

// ============================================================================
// Test Run Tracking
// ============================================================================

/// Status of a test run session
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum TestRunStatus {
    Running,
    Completed,
    Crashed,
    TimedOut,
    Interrupted,
}

impl std::fmt::Display for TestRunStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TestRunStatus::Running => write!(f, "running"),
            TestRunStatus::Completed => write!(f, "completed"),
            TestRunStatus::Crashed => write!(f, "crashed"),
            TestRunStatus::TimedOut => write!(f, "timed_out"),
            TestRunStatus::Interrupted => write!(f, "interrupted"),
        }
    }
}

impl TestRunStatus {
    pub fn parse_str(s: &str) -> Self {
        match s {
            "running" => TestRunStatus::Running,
            "completed" => TestRunStatus::Completed,
            "crashed" => TestRunStatus::Crashed,
            "timed_out" => TestRunStatus::TimedOut,
            "interrupted" => TestRunStatus::Interrupted,
            _ => TestRunStatus::Running,
        }
    }
}

/// A test run record
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TestRunRecord {
    pub run_id: String,
    pub start_time: String,
    pub end_time: String,
    pub pid: u32,
    pub hostname: String,
    pub status: TestRunStatus,
    pub test_count: usize,
    pub passed: usize,
    pub failed: usize,
    pub crashed: usize,
    pub timed_out: usize,
}

impl TestRunRecord {
    pub fn new_running() -> Self {
        let now = chrono::Utc::now();
        TestRunRecord {
            run_id: format!("run_{}", now.format("%Y%m%d_%H%M%S_%3f")),
            start_time: now.to_rfc3339(),
            end_time: String::new(),
            pid: std::process::id(),
            hostname: hostname::get()
                .map(|h| h.to_string_lossy().to_string())
                .unwrap_or_else(|_| "unknown".to_string()),
            status: TestRunStatus::Running,
            test_count: 0,
            passed: 0,
            failed: 0,
            crashed: 0,
            timed_out: 0,
        }
    }

    pub fn mark_completed(&mut self) {
        self.end_time = chrono::Utc::now().to_rfc3339();
        self.status = TestRunStatus::Completed;
    }

    pub fn mark_crashed(&mut self) {
        self.end_time = chrono::Utc::now().to_rfc3339();
        self.status = TestRunStatus::Crashed;
    }

    pub fn is_stale(&self, max_hours: i64) -> bool {
        if self.status != TestRunStatus::Running {
            return false;
        }
        if let Ok(start) = chrono::DateTime::parse_from_rfc3339(&self.start_time) {
            let elapsed = chrono::Utc::now().signed_duration_since(start);
            return elapsed.num_hours() >= max_hours;
        }
        false
    }

    pub fn is_process_alive(&self) -> bool {
        #[cfg(unix)]
        {
            unsafe { libc::kill(self.pid as i32, 0) == 0 }
        }
        #[cfg(not(unix))]
        {
            true
        }
    }

    pub fn validate_record(&self) -> crate::unified_db::IntegrityReport {
        use crate::unified_db::{IntegrityReport, IntegrityViolation, ViolationType};

        let mut report = IntegrityReport::new(&self.run_id);

        if self.status == TestRunStatus::Running && self.is_stale(2) {
            report.add_violation(
                IntegrityViolation::new(
                    ViolationType::StaleRunning,
                    "status",
                    format!("Run has been 'running' for >2 hours (started: {})", self.start_time),
                )
                .with_expected("Completed or Crashed")
                .with_actual("Running"),
            );
            report = report.mark_auto_fixable();
        }

        if self.status == TestRunStatus::Running && !self.is_process_alive() {
            report.add_violation(
                IntegrityViolation::new(
                    ViolationType::DeadProcess,
                    "pid",
                    format!("Process {} is not running but status is 'running'", self.pid),
                )
                .with_expected("Running process or Crashed status")
                .with_actual(format!("Dead process, status={:?}", self.status)),
            );
            report = report.mark_auto_fixable();
        }

        match chrono::DateTime::parse_from_rfc3339(&self.start_time) {
            Ok(start) => {
                if start > chrono::Utc::now() {
                    report.add_violation(
                        IntegrityViolation::new(
                            ViolationType::FutureTimestamp,
                            "start_time",
                            "Start time is in the future",
                        )
                        .with_expected("Past or present")
                        .with_actual(self.start_time.clone()),
                    );
                }

                if !self.end_time.is_empty() {
                    match chrono::DateTime::parse_from_rfc3339(&self.end_time) {
                        Ok(end) => {
                            if end <= start {
                                report.add_violation(
                                    IntegrityViolation::new(
                                        ViolationType::TimestampInconsistent,
                                        "end_time",
                                        "End time is before or equal to start time",
                                    )
                                    .with_expected(format!("After {}", self.start_time))
                                    .with_actual(self.end_time.clone()),
                                );
                            }
                        }
                        Err(e) => {
                            report.add_violation(
                                IntegrityViolation::new(
                                    ViolationType::InvalidValue,
                                    "end_time",
                                    format!("Invalid timestamp format: {}", e),
                                )
                                .with_actual(self.end_time.clone()),
                            );
                        }
                    }
                }
            }
            Err(e) => {
                report.add_violation(
                    IntegrityViolation::new(
                        ViolationType::InvalidValue,
                        "start_time",
                        format!("Invalid timestamp format: {}", e),
                    )
                    .with_actual(self.start_time.clone()),
                );
            }
        }

        let sum = self.passed + self.failed + self.crashed + self.timed_out;
        if sum > self.test_count {
            report.add_violation(
                IntegrityViolation::new(
                    ViolationType::CountInconsistent,
                    "test_count",
                    format!(
                        "Sum of results ({}) exceeds total test count ({})",
                        sum, self.test_count
                    ),
                )
                .with_expected(format!("≥ {}", sum))
                .with_actual(self.test_count.to_string()),
            );
        }

        match self.status {
            TestRunStatus::Completed
            | TestRunStatus::Crashed
            | TestRunStatus::TimedOut
            | TestRunStatus::Interrupted => {
                if self.end_time.is_empty() {
                    report.add_violation(
                        IntegrityViolation::new(
                            ViolationType::StatusInconsistent,
                            "end_time",
                            format!("Status is {:?} but end_time is empty", self.status),
                        )
                        .with_expected("Non-empty timestamp")
                        .with_actual("(empty)"),
                    );
                }
            }
            TestRunStatus::Running => {
                if !self.end_time.is_empty() {
                    report.add_violation(
                        IntegrityViolation::new(
                            ViolationType::StatusInconsistent,
                            "end_time",
                            "Status is Running but end_time is set",
                        )
                        .with_expected("(empty)")
                        .with_actual(self.end_time.clone()),
                    );
                }
            }
        }

        report
    }
}

impl Record for TestRunRecord {
    fn id(&self) -> String {
        self.run_id.clone()
    }

    fn table_name() -> &'static str {
        "test_runs"
    }

    fn field_names() -> &'static [&'static str] {
        &[
            "run_id",
            "start_time",
            "end_time",
            "pid",
            "hostname",
            "status",
            "test_count",
            "passed",
            "failed",
            "crashed",
            "timed_out",
        ]
    }

    fn from_sdn_row(row: &[String]) -> Result<Self, String> {
        Ok(TestRunRecord {
            run_id: row.first().cloned().unwrap_or_default(),
            start_time: row.get(1).cloned().unwrap_or_default(),
            end_time: row.get(2).cloned().unwrap_or_default(),
            pid: row.get(3).and_then(|s| s.parse().ok()).unwrap_or(0),
            hostname: row.get(4).cloned().unwrap_or_default(),
            status: TestRunStatus::parse_str(row.get(5).map(|s| s.as_str()).unwrap_or("running")),
            test_count: row.get(6).and_then(|s| s.parse().ok()).unwrap_or(0),
            passed: row.get(7).and_then(|s| s.parse().ok()).unwrap_or(0),
            failed: row.get(8).and_then(|s| s.parse().ok()).unwrap_or(0),
            crashed: row.get(9).and_then(|s| s.parse().ok()).unwrap_or(0),
            timed_out: row.get(10).and_then(|s| s.parse().ok()).unwrap_or(0),
        })
    }

    fn to_sdn_row(&self) -> Vec<String> {
        vec![
            self.run_id.clone(),
            self.start_time.clone(),
            self.end_time.clone(),
            self.pid.to_string(),
            self.hostname.clone(),
            self.status.to_string(),
            self.test_count.to_string(),
            self.passed.to_string(),
            self.failed.to_string(),
            self.crashed.to_string(),
            self.timed_out.to_string(),
        ]
    }

    fn validate(&self) -> crate::unified_db::IntegrityReport {
        self.validate_record()
    }
}
