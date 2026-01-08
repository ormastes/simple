//! Runtime profiler tests

#[cfg(test)]
mod tests {
    use super::super::*;
    use std::thread;
    use std::time::Duration;

        let profiler = RuntimeProfiler::new(ProfileConfig {
            sample_rate: 1, // Sample every call
            ..Default::default()
        });

        profiler.start();

        // Record some calls
        for _ in 0..100 {
            profiler.record_call("hot_function");
        }
        for _ in 0..5 {
            profiler.record_call("cold_function");
        }

        profiler.stop();

        let metrics = profiler.collect_metrics();
        assert_eq!(metrics.unique_functions, 2);
        assert!(metrics.total_calls >= 100);
    }

    #[test]
    fn test_phase_inference() {
        let profiler = RuntimeProfiler::new(ProfileConfig {
            sample_rate: 1,
            hot_threshold: 10.0,
            cold_threshold: 0.5,
            ..Default::default()
        });

        profiler.start();

        // Simulate startup function (called once at start)
        profiler.record_call("init");

        // Wait a bit then call hot function many times
        std::thread::sleep(std::time::Duration::from_millis(10));
        for _ in 0..1000 {
            profiler.record_call("render");
        }

        profiler.stop();

        let metrics = profiler.collect_metrics();

        // Find the functions
        let init_stat = metrics.function_stats.iter().find(|s| s.name == "init");
        let render_stat = metrics.function_stats.iter().find(|s| s.name == "render");

        assert!(init_stat.is_some());
        assert!(render_stat.is_some());

        // Init should be startup, render should be steady
        assert_eq!(init_stat.unwrap().inferred_phase, LayoutPhase::Startup);
        assert_eq!(render_stat.unwrap().inferred_phase, LayoutPhase::Steady);
    }

    #[test]
    fn test_layout_feedback() {
        let profiler = RuntimeProfiler::new(ProfileConfig {
            sample_rate: 1,
            min_samples: 10,
            ..Default::default()
        });

        profiler.start();

        // Generate enough samples
        profiler.record_call("startup_func");
        for _ in 0..100 {
            profiler.record_call("hot_func");
        }

        profiler.stop();

        let feedback = profiler.generate_layout_feedback();

        assert!(feedback.has_recommendations());
        assert!(feedback.confidence > 0.0);
    }

    #[test]
    fn test_feedback_to_sdn() {
        let feedback = LayoutFeedback {
            promote_to_startup: vec!["init".to_string()],
            promote_to_steady: vec!["render".to_string(), "update".to_string()],
            demote_to_cold: vec!["debug".to_string()],
            confidence: 0.85,
            sample_count: 10000,
            ..Default::default()
        };

        let sdn = feedback.to_sdn();

        assert!(sdn.contains("init: startup"));
        assert!(sdn.contains("render: steady"));
        assert!(sdn.contains("debug: cold"));
        assert!(sdn.contains("85.0%"));
    }

    #[test]
    fn test_sample_rate() {
        let profiler = RuntimeProfiler::new(ProfileConfig {
            sample_rate: 10, // Sample 1 in 10
            ..Default::default()
        });

        profiler.start();

        for _ in 0..100 {
            profiler.record_call("test_func");
        }

        profiler.stop();

        let metrics = profiler.collect_metrics();
        // Should have roughly 10 samples (100 / 10)
        assert!(metrics.total_calls >= 5 && metrics.total_calls <= 15);
    }

    #[test]
    fn test_metrics_top_hot() {
        let profiler = RuntimeProfiler::new(ProfileConfig {
            sample_rate: 1,
            ..Default::default()
        });

        profiler.start();

        for _ in 0..100 {
            profiler.record_call("very_hot");
        }
        for _ in 0..50 {
            profiler.record_call("somewhat_hot");
        }
        for _ in 0..10 {
            profiler.record_call("lukewarm");
        }

        profiler.stop();

        let metrics = profiler.collect_metrics();
        let top = metrics.top_hot_functions(2);

        assert_eq!(top.len(), 2);
        assert_eq!(top[0].name, "very_hot");
        assert_eq!(top[1].name, "somewhat_hot");
    }
}
}
