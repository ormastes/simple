//! HTTP Response Builder
//!
//! Provides a fluent API for constructing HTTP responses with proper headers,
//! status codes, and body content.

use super::http_status::StatusCode;
use std::collections::HashMap;

/// HTTP Response structure
#[derive(Debug, Clone)]
pub struct Response {
    /// HTTP status code
    pub status: StatusCode,
    /// Response headers
    pub headers: HashMap<String, String>,
    /// Response body
    pub body: Vec<u8>,
}

impl Response {
    /// Create a new response builder
    pub fn new() -> ResponseBuilder {
        ResponseBuilder::new()
    }

    /// Create a response with status code
    pub fn with_status(status: StatusCode) -> ResponseBuilder {
        ResponseBuilder::new().status(status)
    }

    /// Create a 200 OK response
    pub fn ok() -> ResponseBuilder {
        ResponseBuilder::new().status(StatusCode::Ok)
    }

    /// Create a 201 Created response
    pub fn created() -> ResponseBuilder {
        ResponseBuilder::new().status(StatusCode::Created)
    }

    /// Create a 204 No Content response
    pub fn no_content() -> ResponseBuilder {
        ResponseBuilder::new().status(StatusCode::NoContent)
    }

    /// Create a 400 Bad Request response
    pub fn bad_request() -> ResponseBuilder {
        ResponseBuilder::new().status(StatusCode::BadRequest)
    }

    /// Create a 401 Unauthorized response
    pub fn unauthorized() -> ResponseBuilder {
        ResponseBuilder::new().status(StatusCode::Unauthorized)
    }

    /// Create a 403 Forbidden response
    pub fn forbidden() -> ResponseBuilder {
        ResponseBuilder::new().status(StatusCode::Forbidden)
    }

    /// Create a 404 Not Found response
    pub fn not_found() -> ResponseBuilder {
        ResponseBuilder::new().status(StatusCode::NotFound)
    }

    /// Create a 500 Internal Server Error response
    pub fn internal_server_error() -> ResponseBuilder {
        ResponseBuilder::new().status(StatusCode::InternalServerError)
    }

    /// Create a 503 Service Unavailable response
    pub fn service_unavailable() -> ResponseBuilder {
        ResponseBuilder::new().status(StatusCode::ServiceUnavailable)
    }
}

impl Default for Response {
    fn default() -> Self {
        Self {
            status: StatusCode::Ok,
            headers: HashMap::new(),
            body: Vec::new(),
        }
    }
}

/// Fluent API builder for HTTP responses
#[derive(Debug, Clone)]
pub struct ResponseBuilder {
    response: Response,
}

impl ResponseBuilder {
    /// Create a new response builder
    pub fn new() -> Self {
        Self {
            response: Response::default(),
        }
    }

    /// Set the status code
    pub fn status(mut self, status: StatusCode) -> Self {
        self.response.status = status;
        self
    }

    /// Add a header
    pub fn header(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.response.headers.insert(key.into(), value.into());
        self
    }

    /// Set Content-Type header
    pub fn content_type(self, content_type: &str) -> Self {
        self.header("Content-Type", content_type)
    }

    /// Set Content-Type to application/json
    pub fn json(self) -> Self {
        self.content_type("application/json")
    }

    /// Set Content-Type to text/html
    pub fn html(self) -> Self {
        self.content_type("text/html; charset=utf-8")
    }

    /// Set Content-Type to text/plain
    pub fn text(self) -> Self {
        self.content_type("text/plain; charset=utf-8")
    }

    /// Set Content-Type to application/xml
    pub fn xml(self) -> Self {
        self.content_type("application/xml")
    }

    /// Set the response body from bytes
    pub fn body(mut self, body: Vec<u8>) -> Self {
        self.response.body = body;
        self
    }

    /// Set the response body from string
    pub fn body_string(mut self, body: impl Into<String>) -> Self {
        self.response.body = body.into().into_bytes();
        self
    }

    /// Set the response body from JSON (serialized string)
    pub fn body_json(mut self, json: impl Into<String>) -> Self {
        self.response.body = json.into().into_bytes();
        self.content_type("application/json")
    }

    /// Add multiple headers at once
    pub fn headers(mut self, headers: HashMap<String, String>) -> Self {
        self.response.headers.extend(headers);
        self
    }

    /// Set a cookie
    pub fn cookie(self, name: &str, value: &str) -> Self {
        self.header("Set-Cookie", format!("{}={}", name, value))
    }

    /// Set a cookie with attributes
    pub fn cookie_with_attrs(self, name: &str, value: &str, attrs: &[(&str, &str)]) -> Self {
        let mut cookie = format!("{}={}", name, value);
        for (key, val) in attrs {
            cookie.push_str(&format!("; {}={}", key, val));
        }
        self.header("Set-Cookie", cookie)
    }

    /// Set Location header for redirects
    pub fn location(self, location: &str) -> Self {
        self.header("Location", location)
    }

    /// Create a redirect response (302 Found by default)
    pub fn redirect(self, location: &str) -> Self {
        self.status(StatusCode::Found).location(location)
    }

    /// Create a permanent redirect (301)
    pub fn redirect_permanent(self, location: &str) -> Self {
        self.status(StatusCode::MovedPermanently).location(location)
    }

    /// Set Cache-Control header
    pub fn cache_control(self, directive: &str) -> Self {
        self.header("Cache-Control", directive)
    }

    /// Disable caching
    pub fn no_cache(self) -> Self {
        self.cache_control("no-cache, no-store, must-revalidate")
    }

    /// Enable CORS with specific origin
    pub fn cors(self, origin: &str) -> Self {
        self.header("Access-Control-Allow-Origin", origin)
    }

    /// Enable CORS for all origins
    pub fn cors_any(self) -> Self {
        self.cors("*")
    }

    /// Build the final response
    pub fn build(self) -> Response {
        self.response
    }
}

impl Default for ResponseBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_response() {
        let response = Response::ok().body_string("Hello, World!").build();

        assert_eq!(response.status, StatusCode::Ok);
        assert_eq!(response.body, b"Hello, World!");
    }

    #[test]
    fn test_json_response() {
        let response = Response::ok()
            .json()
            .body_json(r#"{"message": "success"}"#)
            .build();

        assert_eq!(response.status, StatusCode::Ok);
        assert_eq!(
            response.headers.get("Content-Type").unwrap(),
            "application/json"
        );
        assert_eq!(response.body, br#"{"message": "success"}"#);
    }

    #[test]
    fn test_error_responses() {
        let not_found = Response::not_found()
            .text()
            .body_string("Page not found")
            .build();

        assert_eq!(not_found.status, StatusCode::NotFound);
        assert!(not_found.status.is_client_error());

        let server_error = Response::internal_server_error()
            .text()
            .body_string("Internal error")
            .build();

        assert_eq!(server_error.status, StatusCode::InternalServerError);
        assert!(server_error.status.is_server_error());
    }

    #[test]
    fn test_redirect() {
        let response = Response::new().redirect("/new-location").build();

        assert_eq!(response.status, StatusCode::Found);
        assert_eq!(response.headers.get("Location").unwrap(), "/new-location");
    }

    #[test]
    fn test_permanent_redirect() {
        let response = Response::new().redirect_permanent("/moved").build();

        assert_eq!(response.status, StatusCode::MovedPermanently);
        assert_eq!(response.headers.get("Location").unwrap(), "/moved");
    }

    #[test]
    fn test_headers() {
        let response = Response::ok()
            .header("X-Custom", "value")
            .header("X-Request-ID", "12345")
            .build();

        assert_eq!(response.headers.get("X-Custom").unwrap(), "value");
        assert_eq!(response.headers.get("X-Request-ID").unwrap(), "12345");
    }

    #[test]
    fn test_content_types() {
        let html = Response::ok().html().build();
        assert_eq!(
            html.headers.get("Content-Type").unwrap(),
            "text/html; charset=utf-8"
        );

        let json = Response::ok().json().build();
        assert_eq!(
            json.headers.get("Content-Type").unwrap(),
            "application/json"
        );

        let text = Response::ok().text().build();
        assert_eq!(
            text.headers.get("Content-Type").unwrap(),
            "text/plain; charset=utf-8"
        );
    }

    #[test]
    fn test_cors() {
        let response = Response::ok().cors("https://example.com").build();

        assert_eq!(
            response.headers.get("Access-Control-Allow-Origin").unwrap(),
            "https://example.com"
        );
    }

    #[test]
    fn test_no_cache() {
        let response = Response::ok().no_cache().build();

        assert_eq!(
            response.headers.get("Cache-Control").unwrap(),
            "no-cache, no-store, must-revalidate"
        );
    }

    #[test]
    fn test_cookie() {
        let response = Response::ok().cookie("session_id", "abc123").build();

        assert_eq!(
            response.headers.get("Set-Cookie").unwrap(),
            "session_id=abc123"
        );
    }

    #[test]
    fn test_fluent_chaining() {
        let response = Response::created()
            .json()
            .header("X-Created-By", "test")
            .body_json(r#"{"id": 123}"#)
            .cors_any()
            .build();

        assert_eq!(response.status, StatusCode::Created);
        assert_eq!(
            response.headers.get("Content-Type").unwrap(),
            "application/json"
        );
        assert_eq!(response.headers.get("X-Created-By").unwrap(), "test");
        assert_eq!(
            response.headers.get("Access-Control-Allow-Origin").unwrap(),
            "*"
        );
        assert_eq!(response.body, br#"{"id": 123}"#);
    }
}
