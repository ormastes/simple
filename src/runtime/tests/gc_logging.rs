use std::sync::{Arc, Mutex};

use simple_runtime::gc::{GcLogEventKind, GcRuntime};

#[test]
fn verbose_logging_emits_collection_markers() {
    let events: Arc<Mutex<Vec<String>>> = Arc::new(Mutex::new(Vec::new()));
    let sink = {
        let events = events.clone();
        move |event: simple_runtime::gc::GcLogEvent| {
            events.lock().unwrap().push(event.to_string());
        }
    };

    let gc = GcRuntime::with_logger(sink);
    let _root = gc.allocate(vec![1u8, 2, 3, 4, 5]);
    gc.collect("test-collect");

    let logs = events.lock().unwrap();
    assert!(
        logs.iter().any(|l| l.contains("gc:start reason=test-collect")),
        "expected start log"
    );
    assert!(
        logs.iter().any(|l| l.contains("gc:end reason=test-collect")),
        "expected end log"
    );
}

#[test]
fn structured_events_are_emitted() {
    use simple_runtime::gc::GcLogEvent;
    let events: Arc<Mutex<Vec<GcLogEvent>>> = Arc::new(Mutex::new(Vec::new()));
    let sink = {
        let events = events.clone();
        move |event: GcLogEvent| {
            events.lock().unwrap().push(event);
        }
    };
    let gc = GcRuntime::with_logger(sink);
    let _a = gc.allocate(123u32);
    gc.collect("structured");

    let logs = events.lock().unwrap();
    assert!(logs.iter().any(|e| e.kind == GcLogEventKind::Allocation));
    assert!(logs.iter().any(|e| e.kind == GcLogEventKind::CollectionStart));
    assert!(logs.iter().any(|e| e.kind == GcLogEventKind::CollectionEnd));
}
