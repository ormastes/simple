//! Browser API mock for testing WASM modules
//!
//! Provides mock implementations of browser APIs (Console, DOM, Fetch) for testing
//! WASM modules that expect browser environments. Follows the same fluent API patterns
//! as `simple_mock_helper` for consistency.
//!
//! # Architecture
//!
//! ```text
//! WASM Module (calls browser APIs)
//!       ↓
//! BrowserMock (captures calls)
//!       ↓
//! BrowserVerify (assertion API)
//! ```
//!
//! # Example
//!
//! ```rust
//! use simple_wasm_runtime::browser_mock::{BrowserMock, BrowserVerify};
//!
//! // Setup browser mock
//! let mut mock = BrowserMock::new();
//! mock.console()
//!     .when_log()
//!     .with_args(&["Hello"])
//!     .capture();
//!
//! mock.dom()
//!     .when_get_element_by_id("button")
//!     .returns_element("button", "HTMLButtonElement");
//!
//! // Run WASM with mock environment
//! // ... execute WASM ...
//!
//! // Verify calls
//! let verify = BrowserVerify::new(&mock);
//! verify.console()
//!     .log_was_called()
//!     .with_args(&["Hello"])
//!     .times(1);
//! ```

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

/// Main browser mock setup
#[derive(Debug, Clone)]
pub struct BrowserMock {
    console_calls: Arc<Mutex<Vec<ConsoleCall>>>,
    dom_elements: Arc<Mutex<HashMap<String, DomElement>>>,
    fetch_responses: Arc<Mutex<HashMap<String, FetchResponse>>>,
}

impl BrowserMock {
    /// Create a new browser mock
    pub fn new() -> Self {
        Self {
            console_calls: Arc::new(Mutex::new(Vec::new())),
            dom_elements: Arc::new(Mutex::new(HashMap::new())),
            fetch_responses: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    /// Setup console API mock
    pub fn console(&mut self) -> ConsoleMockSetup {
        ConsoleMockSetup {
            calls: self.console_calls.clone(),
            pending_call: None,
        }
    }

    /// Setup DOM API mock
    pub fn dom(&mut self) -> DomMockSetup {
        DomMockSetup {
            elements: self.dom_elements.clone(),
            pending_element: None,
        }
    }

    /// Setup Fetch API mock
    pub fn fetch(&mut self) -> FetchMockSetup {
        FetchMockSetup {
            responses: self.fetch_responses.clone(),
            pending_response: None,
        }
    }

    /// Clear all recorded calls and mocks
    pub fn reset(&mut self) {
        self.console_calls.lock().unwrap().clear();
        self.dom_elements.lock().unwrap().clear();
        self.fetch_responses.lock().unwrap().clear();
    }
}

impl Default for BrowserMock {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// Console API Mock
// ============================================================================

/// Console call record
#[derive(Debug, Clone, PartialEq)]
pub struct ConsoleCall {
    pub method: ConsoleMethod,
    pub args: Vec<String>,
}

/// Console method types
#[derive(Debug, Clone, PartialEq)]
pub enum ConsoleMethod {
    Log,
    Warn,
    Error,
    Info,
    Debug,
}

/// Fluent builder for console mock setup
pub struct ConsoleMockSetup {
    calls: Arc<Mutex<Vec<ConsoleCall>>>,
    pending_call: Option<ConsoleCall>,
}

impl ConsoleMockSetup {
    /// Setup mock for console.log()
    pub fn when_log(&mut self) -> &mut Self {
        self.pending_call = Some(ConsoleCall {
            method: ConsoleMethod::Log,
            args: Vec::new(),
        });
        self
    }

    /// Setup mock for console.warn()
    pub fn when_warn(&mut self) -> &mut Self {
        self.pending_call = Some(ConsoleCall {
            method: ConsoleMethod::Warn,
            args: Vec::new(),
        });
        self
    }

    /// Setup mock for console.error()
    pub fn when_error(&mut self) -> &mut Self {
        self.pending_call = Some(ConsoleCall {
            method: ConsoleMethod::Error,
            args: Vec::new(),
        });
        self
    }

    /// Set expected arguments for console call
    pub fn with_args(&mut self, args: &[impl ToString]) -> &mut Self {
        if let Some(ref mut call) = self.pending_call {
            call.args = args.iter().map(|a| a.to_string()).collect();
        }
        self
    }

    /// Capture this console call when it occurs
    pub fn capture(&mut self) {
        if let Some(call) = self.pending_call.take() {
            self.calls.lock().unwrap().push(call);
        }
    }

    /// Record a console call (used internally by WASM runtime)
    pub fn record_call(&mut self, method: ConsoleMethod, args: Vec<String>) {
        self.calls.lock().unwrap().push(ConsoleCall { method, args });
    }
}

// ============================================================================
// DOM API Mock
// ============================================================================

/// DOM element representation
#[derive(Debug, Clone, PartialEq)]
pub struct DomElement {
    pub id: String,
    pub tag_name: String,
    pub text_content: Option<String>,
    pub attributes: HashMap<String, String>,
    pub event_listeners: Vec<String>,
}

impl DomElement {
    /// Create a new DOM element
    pub fn new(id: impl Into<String>, tag_name: impl Into<String>) -> Self {
        Self {
            id: id.into(),
            tag_name: tag_name.into(),
            text_content: None,
            attributes: HashMap::new(),
            event_listeners: Vec::new(),
        }
    }

    /// Set text content
    pub fn with_text(mut self, text: impl Into<String>) -> Self {
        self.text_content = Some(text.into());
        self
    }

    /// Add attribute
    pub fn with_attribute(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.attributes.insert(key.into(), value.into());
        self
    }
}

/// Fluent builder for DOM mock setup
pub struct DomMockSetup {
    elements: Arc<Mutex<HashMap<String, DomElement>>>,
    pending_element: Option<(String, DomElement)>,
}

impl DomMockSetup {
    /// Setup mock for document.getElementById()
    pub fn when_get_element_by_id(&mut self, id: impl Into<String>) -> &mut Self {
        let id_str = id.into();
        self.pending_element = Some((id_str.clone(), DomElement::new(&id_str, "div")));
        self
    }

    /// Set the returned element's tag name
    pub fn returns_element(&mut self, id: impl Into<String>, tag_name: impl Into<String>) -> &mut Self {
        let id_str = id.into();
        self.pending_element = Some((id_str.clone(), DomElement::new(&id_str, tag_name)));
        self
    }

    /// Set text content for the element
    pub fn with_text(&mut self, text: impl Into<String>) -> &mut Self {
        if let Some((_, ref mut elem)) = self.pending_element {
            elem.text_content = Some(text.into());
        }
        self
    }

    /// Add attribute to the element
    pub fn with_attribute(&mut self, key: impl Into<String>, value: impl Into<String>) -> &mut Self {
        if let Some((_, ref mut elem)) = self.pending_element {
            elem.attributes.insert(key.into(), value.into());
        }
        self
    }

    /// Finalize the element mock
    pub fn register(&mut self) {
        if let Some((id, elem)) = self.pending_element.take() {
            self.elements.lock().unwrap().insert(id, elem);
        }
    }

    /// Get an element by ID (used internally by WASM runtime)
    pub fn get_element(&self, id: &str) -> Option<DomElement> {
        self.elements.lock().unwrap().get(id).cloned()
    }

    /// Record event listener (used internally by WASM runtime)
    pub fn add_event_listener(&mut self, element_id: &str, event_type: impl Into<String>) {
        if let Some(elem) = self.elements.lock().unwrap().get_mut(element_id) {
            elem.event_listeners.push(event_type.into());
        }
    }
}

// ============================================================================
// Fetch API Mock
// ============================================================================

/// Fetch response representation
#[derive(Debug, Clone, PartialEq)]
pub struct FetchResponse {
    pub url: String,
    pub status: u16,
    pub body: String,
    pub headers: HashMap<String, String>,
}

impl FetchResponse {
    /// Create a new fetch response
    pub fn new(url: impl Into<String>) -> Self {
        Self {
            url: url.into(),
            status: 200,
            body: String::new(),
            headers: HashMap::new(),
        }
    }

    /// Set status code
    pub fn with_status(mut self, status: u16) -> Self {
        self.status = status;
        self
    }

    /// Set response body
    pub fn with_body(mut self, body: impl Into<String>) -> Self {
        self.body = body.into();
        self
    }

    /// Add response header
    pub fn with_header(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.headers.insert(key.into(), value.into());
        self
    }
}

/// Fluent builder for Fetch mock setup
pub struct FetchMockSetup {
    responses: Arc<Mutex<HashMap<String, FetchResponse>>>,
    pending_response: Option<(String, FetchResponse)>,
}

impl FetchMockSetup {
    /// Setup mock for fetch() to a specific URL
    pub fn when_get(&mut self, url: impl Into<String>) -> &mut Self {
        let url_str = url.into();
        self.pending_response = Some((url_str.clone(), FetchResponse::new(&url_str)));
        self
    }

    /// Setup mock for fetch() POST request
    pub fn when_post(&mut self, url: impl Into<String>) -> &mut Self {
        let url_str = url.into();
        self.pending_response = Some((url_str.clone(), FetchResponse::new(&url_str)));
        self
    }

    /// Set response status
    pub fn returns_status(&mut self, status: u16) -> &mut Self {
        if let Some((_, ref mut resp)) = self.pending_response {
            resp.status = status;
        }
        self
    }

    /// Set response body
    pub fn returns_json(&mut self, json: impl Into<String>) -> &mut Self {
        if let Some((_, ref mut resp)) = self.pending_response {
            resp.body = json.into();
            resp.headers
                .insert("Content-Type".to_string(), "application/json".to_string());
        }
        self
    }

    /// Set response body as text
    pub fn returns_text(&mut self, text: impl Into<String>) -> &mut Self {
        if let Some((_, ref mut resp)) = self.pending_response {
            resp.body = text.into();
        }
        self
    }

    /// Add response header
    pub fn with_header(&mut self, key: impl Into<String>, value: impl Into<String>) -> &mut Self {
        if let Some((_, ref mut resp)) = self.pending_response {
            resp.headers.insert(key.into(), value.into());
        }
        self
    }

    /// Register the fetch response mock
    pub fn register(&mut self) {
        if let Some((url, resp)) = self.pending_response.take() {
            self.responses.lock().unwrap().insert(url, resp);
        }
    }

    /// Get mock response for URL (used internally by WASM runtime)
    pub fn get_response(&self, url: &str) -> Option<FetchResponse> {
        self.responses.lock().unwrap().get(url).cloned()
    }
}

// ============================================================================
// Verification API
// ============================================================================

/// Fluent verification API for browser mocks
pub struct BrowserVerify<'a> {
    mock: &'a BrowserMock,
}

impl<'a> BrowserVerify<'a> {
    /// Create a new verifier for a browser mock
    pub fn new(mock: &'a BrowserMock) -> Self {
        Self { mock }
    }

    /// Verify console API calls
    pub fn console(&self) -> ConsoleVerify {
        ConsoleVerify {
            calls: self.mock.console_calls.clone(),
            method_filter: None,
            args_filter: None,
            count_expectation: None,
        }
    }

    /// Verify DOM API interactions
    pub fn dom(&self) -> DomVerify {
        DomVerify {
            elements: self.mock.dom_elements.clone(),
            element_id: None,
        }
    }

    /// Verify Fetch API calls
    pub fn fetch(&self) -> FetchVerify {
        FetchVerify {
            responses: self.mock.fetch_responses.clone(),
            url_filter: None,
        }
    }
}

/// Console call verifier
pub struct ConsoleVerify {
    calls: Arc<Mutex<Vec<ConsoleCall>>>,
    method_filter: Option<ConsoleMethod>,
    args_filter: Option<Vec<String>>,
    count_expectation: Option<usize>,
}

impl ConsoleVerify {
    /// Verify console.log() was called
    pub fn log_was_called(&mut self) -> &mut Self {
        self.method_filter = Some(ConsoleMethod::Log);
        self
    }

    /// Verify console.warn() was called
    pub fn warn_was_called(&mut self) -> &mut Self {
        self.method_filter = Some(ConsoleMethod::Warn);
        self
    }

    /// Verify console.error() was called
    pub fn error_was_called(&mut self) -> &mut Self {
        self.method_filter = Some(ConsoleMethod::Error);
        self
    }

    /// Filter by expected arguments
    pub fn with_args(&mut self, args: &[impl ToString]) -> &mut Self {
        self.args_filter = Some(args.iter().map(|a| a.to_string()).collect());
        self
    }

    /// Expect specific number of calls
    pub fn times(&mut self, count: usize) -> &mut Self {
        self.count_expectation = Some(count);
        self
    }

    /// Execute verification and panic if failed
    pub fn verify(&self) {
        let calls = self.calls.lock().unwrap();
        let matching_calls: Vec<_> = calls
            .iter()
            .filter(|call| {
                let method_match = self.method_filter.as_ref().map_or(true, |m| &call.method == m);
                let args_match = self.args_filter.as_ref().map_or(true, |a| &call.args == a);
                method_match && args_match
            })
            .collect();

        if let Some(expected_count) = self.count_expectation {
            assert_eq!(
                matching_calls.len(),
                expected_count,
                "Expected {} console calls, but found {}",
                expected_count,
                matching_calls.len()
            );
        } else {
            assert!(!matching_calls.is_empty(), "Expected console call but none found");
        }
    }
}

/// DOM verifier
pub struct DomVerify {
    elements: Arc<Mutex<HashMap<String, DomElement>>>,
    element_id: Option<String>,
}

impl DomVerify {
    /// Verify element exists
    pub fn element_exists(&mut self, id: impl Into<String>) -> &mut Self {
        self.element_id = Some(id.into());
        self
    }

    /// Verify element has specific text
    pub fn has_text(&self, expected_text: &str) -> bool {
        if let Some(ref id) = self.element_id {
            if let Some(elem) = self.elements.lock().unwrap().get(id) {
                return elem.text_content.as_ref().map_or(false, |t| t == expected_text);
            }
        }
        false
    }

    /// Verify element has event listener
    pub fn has_listener(&self, event_type: &str) -> bool {
        if let Some(ref id) = self.element_id {
            if let Some(elem) = self.elements.lock().unwrap().get(id) {
                return elem.event_listeners.contains(&event_type.to_string());
            }
        }
        false
    }
}

/// Fetch verifier
pub struct FetchVerify {
    responses: Arc<Mutex<HashMap<String, FetchResponse>>>,
    url_filter: Option<String>,
}

impl FetchVerify {
    /// Verify fetch was called for URL
    pub fn was_called_with_url(&mut self, url: impl Into<String>) -> &mut Self {
        self.url_filter = Some(url.into());
        self
    }

    /// Execute verification
    pub fn verify(&self) {
        if let Some(ref url) = self.url_filter {
            assert!(
                self.responses.lock().unwrap().contains_key(url),
                "Expected fetch to URL '{}' but none found",
                url
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_console_mock_setup() {
        let mut mock = BrowserMock::new();

        // Simulate WASM calling console.log
        mock.console()
            .record_call(ConsoleMethod::Log, vec!["Hello".to_string(), "World".to_string()]);

        let verify = BrowserVerify::new(&mock);
        verify
            .console()
            .log_was_called()
            .with_args(&["Hello", "World"])
            .times(1)
            .verify();
    }

    #[test]
    fn test_dom_mock_setup() {
        let mut mock = BrowserMock::new();
        mock.dom()
            .when_get_element_by_id("button")
            .returns_element("button", "button")
            .with_text("Click me")
            .register();

        let elem = mock.dom().get_element("button").unwrap();
        assert_eq!(elem.tag_name, "button");
        assert_eq!(elem.text_content, Some("Click me".to_string()));
    }

    #[test]
    fn test_fetch_mock_setup() {
        let mut mock = BrowserMock::new();
        mock.fetch()
            .when_get("/api/users")
            .returns_status(200)
            .returns_json(r#"{"users": []}"#)
            .register();

        let resp = mock.fetch().get_response("/api/users").unwrap();
        assert_eq!(resp.status, 200);
        assert_eq!(resp.body, r#"{"users": []}"#);
    }

    #[test]
    fn test_browser_verify() {
        let mut mock = BrowserMock::new();
        mock.console().record_call(ConsoleMethod::Log, vec!["test".to_string()]);

        let verify = BrowserVerify::new(&mock);
        verify.console().log_was_called().times(1).verify();
    }
}
