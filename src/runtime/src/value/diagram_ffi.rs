//! FFI functions for diagram generation and call tracing.
//!
//! These functions allow Simple code to record method calls for
//! generating sequence, class, and architecture diagrams.

use std::ffi::{CStr, CString};
use std::os::raw::c_char;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::OnceLock;

use parking_lot::RwLock;

// ============================================================================
// Diagram Recording State
// ============================================================================

/// Whether diagram recording is enabled
static DIAGRAM_ENABLED: AtomicBool = AtomicBool::new(false);

/// Current test context
static CURRENT_TEST_FILE: OnceLock<RwLock<String>> = OnceLock::new();
static CURRENT_TEST_NAME: OnceLock<RwLock<String>> = OnceLock::new();

fn get_test_file() -> &'static RwLock<String> {
    CURRENT_TEST_FILE.get_or_init(|| RwLock::new(String::new()))
}

fn get_test_name() -> &'static RwLock<String> {
    CURRENT_TEST_NAME.get_or_init(|| RwLock::new(String::new()))
}

/// Call event for recording
#[derive(Debug, Clone)]
pub struct CallEvent {
    pub callee: String,
    pub callee_class: Option<String>,
    pub arguments: Vec<String>,
    pub call_type: CallType,
    pub return_value: Option<String>,
    pub timestamp_ns: u64,
}

/// Call type enum
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(C)]
pub enum CallType {
    Function = 0,
    Method = 1,
    Constructor = 2,
    Return = 3,
}

/// Recorded call events
static CALL_EVENTS: OnceLock<RwLock<Vec<CallEvent>>> = OnceLock::new();

fn get_events() -> &'static RwLock<Vec<CallEvent>> {
    CALL_EVENTS.get_or_init(|| RwLock::new(Vec::new()))
}

/// Architectural entities
static ARCH_ENTITIES: OnceLock<RwLock<Vec<String>>> = OnceLock::new();

fn get_arch_entities() -> &'static RwLock<Vec<String>> {
    ARCH_ENTITIES.get_or_init(|| RwLock::new(Vec::new()))
}

// ============================================================================
// FFI Functions for Diagram Control
// ============================================================================

/// Enable diagram recording
#[no_mangle]
pub extern "C" fn rt_diagram_enable() {
    DIAGRAM_ENABLED.store(true, Ordering::SeqCst);
}

/// Disable diagram recording
#[no_mangle]
pub extern "C" fn rt_diagram_disable() {
    DIAGRAM_ENABLED.store(false, Ordering::SeqCst);
}

/// Check if diagram recording is enabled
#[no_mangle]
pub extern "C" fn rt_diagram_is_enabled() -> bool {
    DIAGRAM_ENABLED.load(Ordering::SeqCst)
}

/// Clear all recorded events
#[no_mangle]
pub extern "C" fn rt_diagram_clear() {
    get_events().write().clear();
    get_arch_entities().write().clear();
}

/// Set current test context
///
/// # Safety
/// `test_file` and `test_name` must be valid C strings
#[no_mangle]
pub unsafe extern "C" fn rt_diagram_set_context(test_file: *const c_char, test_name: *const c_char) {
    if !test_file.is_null() {
        if let Ok(s) = CStr::from_ptr(test_file).to_str() {
            *get_test_file().write() = s.to_string();
        }
    }
    if !test_name.is_null() {
        if let Ok(s) = CStr::from_ptr(test_name).to_str() {
            *get_test_name().write() = s.to_string();
        }
    }
}

/// Clear test context
#[no_mangle]
pub extern "C" fn rt_diagram_clear_context() {
    get_test_file().write().clear();
    get_test_name().write().clear();
}

// ============================================================================
// FFI Functions for Call Recording
// ============================================================================

/// Record a function call
///
/// # Safety
/// `name` must be a valid C string
#[no_mangle]
pub unsafe extern "C" fn rt_diagram_trace_call(name: *const c_char) {
    if !DIAGRAM_ENABLED.load(Ordering::SeqCst) || name.is_null() {
        return;
    }

    let name_str = match CStr::from_ptr(name).to_str() {
        Ok(s) => s.to_string(),
        Err(_) => return,
    };

    let event = CallEvent {
        callee: name_str,
        callee_class: None,
        arguments: vec![],
        call_type: CallType::Function,
        return_value: None,
        timestamp_ns: now_nanos(),
    };

    get_events().write().push(event);
}

/// Record a method call
///
/// # Safety
/// `class_name` and `method_name` must be valid C strings
#[no_mangle]
pub unsafe extern "C" fn rt_diagram_trace_method(
    class_name: *const c_char,
    method_name: *const c_char,
) {
    if !DIAGRAM_ENABLED.load(Ordering::SeqCst) {
        return;
    }

    let class_str = if class_name.is_null() {
        None
    } else {
        CStr::from_ptr(class_name).to_str().ok().map(|s| s.to_string())
    };

    let method_str = if method_name.is_null() {
        return;
    } else {
        match CStr::from_ptr(method_name).to_str() {
            Ok(s) => s.to_string(),
            Err(_) => return,
        }
    };

    let event = CallEvent {
        callee: method_str,
        callee_class: class_str,
        arguments: vec![],
        call_type: CallType::Method,
        return_value: None,
        timestamp_ns: now_nanos(),
    };

    get_events().write().push(event);
}

/// Record a method call with arguments
///
/// # Safety
/// All string pointers must be valid C strings or null
#[no_mangle]
pub unsafe extern "C" fn rt_diagram_trace_method_with_args(
    class_name: *const c_char,
    method_name: *const c_char,
    args: *const c_char,
) {
    if !DIAGRAM_ENABLED.load(Ordering::SeqCst) {
        return;
    }

    let class_str = if class_name.is_null() {
        None
    } else {
        CStr::from_ptr(class_name).to_str().ok().map(|s| s.to_string())
    };

    let method_str = if method_name.is_null() {
        return;
    } else {
        match CStr::from_ptr(method_name).to_str() {
            Ok(s) => s.to_string(),
            Err(_) => return,
        }
    };

    let arguments = if args.is_null() {
        vec![]
    } else {
        match CStr::from_ptr(args).to_str() {
            Ok(s) => s.split(',').map(|a| a.trim().to_string()).collect(),
            Err(_) => vec![],
        }
    };

    let event = CallEvent {
        callee: method_str,
        callee_class: class_str,
        arguments,
        call_type: CallType::Method,
        return_value: None,
        timestamp_ns: now_nanos(),
    };

    get_events().write().push(event);
}

/// Record a return value
///
/// # Safety
/// `value` must be a valid C string or null
#[no_mangle]
pub unsafe extern "C" fn rt_diagram_trace_return(value: *const c_char) {
    if !DIAGRAM_ENABLED.load(Ordering::SeqCst) {
        return;
    }

    let return_value = if value.is_null() {
        None
    } else {
        CStr::from_ptr(value).to_str().ok().map(|s| s.to_string())
    };

    // Update the last event's return value
    let mut events = get_events().write();
    if let Some(last) = events.last_mut() {
        last.return_value = return_value;
    }
}

/// Mark an entity as architectural component
///
/// # Safety
/// `entity` must be a valid C string
#[no_mangle]
pub unsafe extern "C" fn rt_diagram_mark_architectural(entity: *const c_char) {
    if entity.is_null() {
        return;
    }

    let entity_str = match CStr::from_ptr(entity).to_str() {
        Ok(s) => s.to_string(),
        Err(_) => return,
    };

    let mut entities = get_arch_entities().write();
    if !entities.contains(&entity_str) {
        entities.push(entity_str);
    }
}

/// Check if entity is architectural
///
/// # Safety
/// `entity` must be a valid C string
#[no_mangle]
pub unsafe extern "C" fn rt_diagram_is_architectural(entity: *const c_char) -> bool {
    if entity.is_null() {
        return false;
    }

    let entity_str = match CStr::from_ptr(entity).to_str() {
        Ok(s) => s,
        Err(_) => return false,
    };

    get_arch_entities().read().iter().any(|e| e == entity_str)
}

// ============================================================================
// FFI Functions for Diagram Generation
// ============================================================================

/// Get number of recorded events
#[no_mangle]
pub extern "C" fn rt_diagram_event_count() -> usize {
    get_events().read().len()
}

/// Get number of architectural entities
#[no_mangle]
pub extern "C" fn rt_diagram_arch_entity_count() -> usize {
    get_arch_entities().read().len()
}

/// Generate sequence diagram as mermaid string
/// Returns a newly allocated C string that must be freed with rt_diagram_free_string
#[no_mangle]
pub extern "C" fn rt_diagram_generate_sequence() -> *mut c_char {
    let events = get_events().read();
    let mermaid = generate_sequence_mermaid(&events);

    match CString::new(mermaid) {
        Ok(s) => s.into_raw(),
        Err(_) => std::ptr::null_mut(),
    }
}

/// Generate class diagram as mermaid string
/// Returns a newly allocated C string that must be freed with rt_diagram_free_string
#[no_mangle]
pub extern "C" fn rt_diagram_generate_class() -> *mut c_char {
    let events = get_events().read();
    let mermaid = generate_class_mermaid(&events);

    match CString::new(mermaid) {
        Ok(s) => s.into_raw(),
        Err(_) => std::ptr::null_mut(),
    }
}

/// Generate architecture diagram as mermaid string
/// Returns a newly allocated C string that must be freed with rt_diagram_free_string
#[no_mangle]
pub extern "C" fn rt_diagram_generate_arch() -> *mut c_char {
    let events = get_events().read();
    let arch_entities = get_arch_entities().read();
    let mermaid = generate_arch_mermaid(&events, &arch_entities);

    match CString::new(mermaid) {
        Ok(s) => s.into_raw(),
        Err(_) => std::ptr::null_mut(),
    }
}

/// Free a string allocated by diagram generation
///
/// # Safety
/// `s` must be a pointer returned by rt_diagram_generate_* or null
#[no_mangle]
pub unsafe extern "C" fn rt_diagram_free_string(s: *mut c_char) {
    if !s.is_null() {
        drop(CString::from_raw(s));
    }
}

// ============================================================================
// Helper Functions
// ============================================================================

fn now_nanos() -> u64 {
    use std::time::{SystemTime, UNIX_EPOCH};
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_nanos() as u64)
        .unwrap_or(0)
}

fn generate_sequence_mermaid(events: &[CallEvent]) -> String {
    let mut output = String::from("sequenceDiagram\n");

    // Extract participants
    let mut participants: Vec<String> = vec![];
    for event in events {
        if let Some(cls) = &event.callee_class {
            if !participants.contains(cls) {
                participants.push(cls.clone());
            }
        }
    }

    // Add participants
    for p in &participants {
        output.push_str(&format!("    participant {}\n", p));
    }
    output.push('\n');

    // Generate calls
    let mut stack: Vec<String> = vec!["Test".to_string()];
    for event in events {
        if let Some(cls) = &event.callee_class {
            let caller = stack.last().cloned().unwrap_or_else(|| "Test".to_string());

            match event.call_type {
                CallType::Method | CallType::Function => {
                    let args = if event.arguments.is_empty() {
                        String::new()
                    } else {
                        event.arguments.join(", ")
                    };
                    output.push_str(&format!("    {}->>{}:{}{}\n",
                        caller, cls, event.callee,
                        if args.is_empty() { String::new() } else { format!("({})", args) }
                    ));
                    stack.push(cls.clone());
                }
                CallType::Return => {
                    if stack.len() > 1 {
                        stack.pop();
                        let returnee = stack.last().cloned().unwrap_or_else(|| "Test".to_string());
                        let ret_val = event.return_value.as_deref().unwrap_or("void");
                        output.push_str(&format!("    {}-->>{}:{}\n", cls, returnee, ret_val));
                    }
                }
                CallType::Constructor => {
                    output.push_str(&format!("    {}->>{}:new()\n", caller, cls));
                    stack.push(cls.clone());
                }
            }
        }
    }

    output
}

fn generate_class_mermaid(events: &[CallEvent]) -> String {
    let mut output = String::from("classDiagram\n");

    // Extract classes and methods
    let mut classes: std::collections::HashMap<String, Vec<String>> = std::collections::HashMap::new();

    for event in events {
        if let Some(cls) = &event.callee_class {
            let methods = classes.entry(cls.clone()).or_default();
            if !methods.contains(&event.callee) {
                methods.push(event.callee.clone());
            }
        }
    }

    // Generate class definitions
    for (cls, methods) in &classes {
        output.push_str(&format!("    class {} {{\n", cls));
        for method in methods {
            output.push_str(&format!("        +{}()\n", method));
        }
        output.push_str("    }\n");
    }

    // Generate relationships
    let mut relationships: Vec<(String, String)> = vec![];
    let mut last_class: Option<String> = None;

    for event in events {
        if let Some(cls) = &event.callee_class {
            if let Some(prev) = &last_class {
                if prev != cls {
                    let rel = (prev.clone(), cls.clone());
                    if !relationships.contains(&rel) {
                        relationships.push(rel);
                    }
                }
            }
            last_class = Some(cls.clone());
        }
    }

    output.push('\n');
    for (from, to) in &relationships {
        output.push_str(&format!("    {} --> {}\n", from, to));
    }

    output
}

fn generate_arch_mermaid(events: &[CallEvent], arch_entities: &[String]) -> String {
    let mut output = String::from("flowchart TD\n");

    // Add architectural nodes
    for entity in arch_entities {
        if entity.contains('.') {
            let parts: Vec<&str> = entity.split('.').collect();
            let short_name = parts.last().copied().unwrap_or(entity.as_str());
            output.push_str(&format!("    {}[{}]\n", entity.replace('.', "_"), short_name));
        } else {
            output.push_str(&format!("    {}\n", entity));
        }
    }

    // Extract edges from events between architectural entities
    let mut edges: Vec<(String, String)> = vec![];
    let mut last_arch: Option<String> = None;

    for event in events {
        if let Some(cls) = &event.callee_class {
            if arch_entities.contains(cls) {
                if let Some(prev) = &last_arch {
                    if prev != cls {
                        let edge = (prev.clone(), cls.clone());
                        if !edges.contains(&edge) {
                            edges.push(edge);
                        }
                    }
                }
                last_arch = Some(cls.clone());
            }
        }
    }

    output.push('\n');
    for (from, to) in &edges {
        let from_id = from.replace('.', "_");
        let to_id = to.replace('.', "_");
        output.push_str(&format!("    {} --> {}\n", from_id, to_id));
    }

    output
}

// ============================================================================
// Public Rust API (for use from Rust code)
// ============================================================================

/// Enable diagram recording (Rust API)
pub fn enable_diagrams() {
    DIAGRAM_ENABLED.store(true, Ordering::SeqCst);
}

/// Disable diagram recording (Rust API)
pub fn disable_diagrams() {
    DIAGRAM_ENABLED.store(false, Ordering::SeqCst);
}

/// Check if diagrams are enabled (Rust API)
pub fn is_diagram_enabled() -> bool {
    DIAGRAM_ENABLED.load(Ordering::SeqCst)
}

/// Get recorded events (Rust API)
pub fn get_recorded_events() -> Vec<CallEvent> {
    get_events().read().clone()
}

/// Get architectural entities (Rust API)
pub fn get_architectural_entities() -> Vec<String> {
    get_arch_entities().read().clone()
}

/// Clear all recorded data (Rust API)
pub fn clear_diagram_data() {
    get_events().write().clear();
    get_arch_entities().write().clear();
}

/// Trace a function call (Rust API)
pub fn trace_call(name: &str) {
    if !DIAGRAM_ENABLED.load(Ordering::SeqCst) {
        return;
    }

    let event = CallEvent {
        callee: name.to_string(),
        callee_class: None,
        arguments: vec![],
        call_type: CallType::Function,
        return_value: None,
        timestamp_ns: now_nanos(),
    };

    get_events().write().push(event);
}

/// Trace a method call (Rust API)
pub fn trace_method(class_name: &str, method_name: &str) {
    if !DIAGRAM_ENABLED.load(Ordering::SeqCst) {
        return;
    }

    let event = CallEvent {
        callee: method_name.to_string(),
        callee_class: Some(class_name.to_string()),
        arguments: vec![],
        call_type: CallType::Method,
        return_value: None,
        timestamp_ns: now_nanos(),
    };

    get_events().write().push(event);
}

/// Trace a method call with arguments (Rust API)
pub fn trace_method_with_args(class_name: &str, method_name: &str, args: &[String]) {
    if !DIAGRAM_ENABLED.load(Ordering::SeqCst) {
        return;
    }

    let event = CallEvent {
        callee: method_name.to_string(),
        callee_class: Some(class_name.to_string()),
        arguments: args.to_vec(),
        call_type: CallType::Method,
        return_value: None,
        timestamp_ns: now_nanos(),
    };

    get_events().write().push(event);
}

/// Trace a return value (Rust API)
pub fn trace_return(value: Option<&str>) {
    if !DIAGRAM_ENABLED.load(Ordering::SeqCst) {
        return;
    }

    let mut events = get_events().write();
    if let Some(last) = events.last_mut() {
        last.return_value = value.map(|s| s.to_string());
    }
}

/// Mark an entity as architectural (Rust API)
pub fn mark_architectural(entity: &str) {
    let mut entities = get_arch_entities().write();
    if !entities.iter().any(|e| e == entity) {
        entities.push(entity.to_string());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_diagram_enable_disable() {
        rt_diagram_disable();
        assert!(!rt_diagram_is_enabled());

        rt_diagram_enable();
        assert!(rt_diagram_is_enabled());

        rt_diagram_disable();
        assert!(!rt_diagram_is_enabled());
    }

    #[test]
    fn test_trace_method() {
        rt_diagram_clear();
        rt_diagram_enable();

        unsafe {
            let class_name = CString::new("UserService").unwrap();
            let method_name = CString::new("authenticate").unwrap();
            rt_diagram_trace_method(class_name.as_ptr(), method_name.as_ptr());
        }

        assert_eq!(rt_diagram_event_count(), 1);

        let events = get_recorded_events();
        assert_eq!(events[0].callee, "authenticate");
        assert_eq!(events[0].callee_class, Some("UserService".to_string()));

        rt_diagram_disable();
        rt_diagram_clear();
    }

    #[test]
    fn test_generate_sequence() {
        rt_diagram_clear();
        rt_diagram_enable();

        unsafe {
            let class1 = CString::new("Auth").unwrap();
            let method1 = CString::new("login").unwrap();
            rt_diagram_trace_method(class1.as_ptr(), method1.as_ptr());

            let class2 = CString::new("Database").unwrap();
            let method2 = CString::new("query").unwrap();
            rt_diagram_trace_method(class2.as_ptr(), method2.as_ptr());
        }

        let mermaid_ptr = rt_diagram_generate_sequence();
        assert!(!mermaid_ptr.is_null());

        let mermaid = unsafe { CStr::from_ptr(mermaid_ptr).to_str().unwrap() };
        assert!(mermaid.contains("sequenceDiagram"));
        assert!(mermaid.contains("participant Auth"));
        assert!(mermaid.contains("participant Database"));

        unsafe { rt_diagram_free_string(mermaid_ptr); }
        rt_diagram_disable();
        rt_diagram_clear();
    }
}
