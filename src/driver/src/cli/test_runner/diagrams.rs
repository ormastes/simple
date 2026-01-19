//! Diagram generation from test execution.
//!
//! Generates sequence, class, and architecture diagrams from test runs.

use std::path::PathBuf;
use std::fs;

use simple_compiler::runtime_profile::{
    generate_arch_from_events, generate_class_from_events, generate_sequence_from_events,
    global_profiler, DiagramOptions,
};

use super::types::{TestFileResult, TestOptions};

/// Generate diagrams from test execution using the global profiler and diagram_ffi
pub fn generate_test_diagrams(options: &TestOptions, _results: &[TestFileResult], quiet: bool) -> Option<Vec<PathBuf>> {
    use simple_runtime::value::diagram_ffi;

    // Get events from global profiler
    let profiler = global_profiler();
    let profiler_events = profiler.get_sequence_events();
    let profiler_architectural = profiler.get_architectural_entities();

    // Get events from diagram_ffi (interpreter tracing)
    let ffi_events = diagram_ffi::get_recorded_events();
    let ffi_architectural = diagram_ffi::get_architectural_entities();

    // Disable diagram recording
    diagram_ffi::disable_diagrams();

    // Check if we have any events from either source
    let has_profiler_events = !profiler_events.is_empty();
    let has_ffi_events = !ffi_events.is_empty();

    if !has_profiler_events && !has_ffi_events {
        if !quiet {
            println!("No sequence events recorded.");
            println!("Hint: Enable profiling with ProfileConfig::combined() or --diagram-all");
        }
        return None;
    }

    // Use FFI events if available, otherwise fall back to profiler events
    let (events, architectural) = if has_ffi_events {
        // Convert FFI events to profiler format
        use simple_compiler::runtime_profile::{CallType as ProfileCallType, SequenceEvent};
        use std::collections::HashSet;

        let converted_events: Vec<_> = ffi_events
            .iter()
            .enumerate()
            .map(|(idx, e)| SequenceEvent {
                sequence_num: idx as u64,
                timestamp_ns: e.timestamp_ns,
                caller: "Test".to_string(),
                callee: e.callee.clone(),
                caller_class: None,
                callee_class: e.callee_class.clone(),
                arguments: e.arguments.clone(),
                return_value: e.return_value.clone(),
                call_type: match e.call_type {
                    diagram_ffi::CallType::Function => ProfileCallType::Direct,
                    diagram_ffi::CallType::Method => ProfileCallType::Method,
                    diagram_ffi::CallType::Constructor => ProfileCallType::Constructor,
                    diagram_ffi::CallType::Return => ProfileCallType::Direct, // Return is tracked via is_return field
                },
                depth: 0,
                is_return: matches!(e.call_type, diagram_ffi::CallType::Return),
            })
            .collect();
        // Convert Vec to HashSet for architectural entities
        let arch_set: HashSet<String> = ffi_architectural.into_iter().collect();
        (converted_events, arch_set)
    } else {
        (profiler_events, profiler_architectural)
    };

    if !quiet && has_ffi_events {
        println!("Using {} events from interpreter call tracing", ffi_events.len());
    }

    // Setup output directory
    let output_dir = options
        .diagram_output
        .clone()
        .unwrap_or_else(|| PathBuf::from("target/diagrams"));

    if let Err(e) = fs::create_dir_all(&output_dir) {
        if !quiet {
            eprintln!("Failed to create diagram output directory: {}", e);
        }
        return None;
    }

    // Build diagram options
    let mut diagram_opts = DiagramOptions::new()
        .with_timing(true)
        .with_args(true)
        .with_returns(true);

    if let Some(ref include) = options.seq_include {
        for pattern in include.split(',') {
            diagram_opts = diagram_opts.with_include(pattern.trim());
        }
    }
    if let Some(ref exclude) = options.seq_exclude {
        for pattern in exclude.split(',') {
            diagram_opts = diagram_opts.with_exclude(pattern.trim());
        }
    }

    let mut paths = Vec::new();

    // Generate sequence diagram
    if options.seq_diagram || options.diagram_all {
        let content = generate_sequence_from_events(&events, &diagram_opts);
        let path = output_dir.join("test_sequence.md");
        if let Err(e) = fs::write(&path, &content) {
            if !quiet {
                eprintln!("Failed to write sequence diagram: {}", e);
            }
        } else {
            paths.push(path);
        }
    }

    // Generate class diagram
    if options.class_diagram || options.diagram_all {
        let content = generate_class_from_events(&events, &diagram_opts);
        let path = output_dir.join("test_class.md");
        if let Err(e) = fs::write(&path, &content) {
            if !quiet {
                eprintln!("Failed to write class diagram: {}", e);
            }
        } else {
            paths.push(path);
        }
    }

    // Generate architecture diagram
    if options.arch_diagram || options.diagram_all {
        let content = generate_arch_from_events(&events, &architectural, &diagram_opts);
        let path = output_dir.join("test_arch.md");
        if let Err(e) = fs::write(&path, &content) {
            if !quiet {
                eprintln!("Failed to write architecture diagram: {}", e);
            }
        } else {
            paths.push(path);
        }
    }

    if paths.is_empty() {
        None
    } else {
        Some(paths)
    }
}
