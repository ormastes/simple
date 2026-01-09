//! HTTP Status Code Type
//!
//! Implements a type-safe StatusCode enum for HTTP response codes.
//! This provides compile-time validation and semantic meaning for HTTP status values.

/// HTTP Status Code categories
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum StatusCodeCategory {
    /// 1xx: Informational responses
    Informational,
    /// 2xx: Successful responses
    Success,
    /// 3xx: Redirection messages
    Redirection,
    /// 4xx: Client error responses
    ClientError,
    /// 5xx: Server error responses
    ServerError,
}

/// HTTP Status Codes
///
/// This enum provides type-safe representation of all standard HTTP status codes.
/// Each variant includes the numeric code and a canonical reason phrase.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum StatusCode {
    // 1xx Informational
    Continue = 100,
    SwitchingProtocols = 101,
    Processing = 102,
    EarlyHints = 103,

    // 2xx Success
    Ok = 200,
    Created = 201,
    Accepted = 202,
    NonAuthoritativeInformation = 203,
    NoContent = 204,
    ResetContent = 205,
    PartialContent = 206,
    MultiStatus = 207,
    AlreadyReported = 208,
    ImUsed = 226,

    // 3xx Redirection
    MultipleChoices = 300,
    MovedPermanently = 301,
    Found = 302,
    SeeOther = 303,
    NotModified = 304,
    UseProxy = 305,
    TemporaryRedirect = 307,
    PermanentRedirect = 308,

    // 4xx Client Error
    BadRequest = 400,
    Unauthorized = 401,
    PaymentRequired = 402,
    Forbidden = 403,
    NotFound = 404,
    MethodNotAllowed = 405,
    NotAcceptable = 406,
    ProxyAuthenticationRequired = 407,
    RequestTimeout = 408,
    Conflict = 409,
    Gone = 410,
    LengthRequired = 411,
    PreconditionFailed = 412,
    PayloadTooLarge = 413,
    UriTooLong = 414,
    UnsupportedMediaType = 415,
    RangeNotSatisfiable = 416,
    ExpectationFailed = 417,
    ImATeapot = 418,
    MisdirectedRequest = 421,
    UnprocessableEntity = 422,
    Locked = 423,
    FailedDependency = 424,
    TooEarly = 425,
    UpgradeRequired = 426,
    PreconditionRequired = 428,
    TooManyRequests = 429,
    RequestHeaderFieldsTooLarge = 431,
    UnavailableForLegalReasons = 451,

    // 5xx Server Error
    InternalServerError = 500,
    NotImplemented = 501,
    BadGateway = 502,
    ServiceUnavailable = 503,
    GatewayTimeout = 504,
    HttpVersionNotSupported = 505,
    VariantAlsoNegotiates = 506,
    InsufficientStorage = 507,
    LoopDetected = 508,
    NotExtended = 510,
    NetworkAuthenticationRequired = 511,
}

impl StatusCode {
    /// Get the numeric status code
    pub fn as_u16(&self) -> u16 {
        *self as u16
    }

    /// Get the category of this status code
    pub fn category(&self) -> StatusCodeCategory {
        match self.as_u16() {
            100..=199 => StatusCodeCategory::Informational,
            200..=299 => StatusCodeCategory::Success,
            300..=399 => StatusCodeCategory::Redirection,
            400..=499 => StatusCodeCategory::ClientError,
            500..=599 => StatusCodeCategory::ServerError,
            _ => StatusCodeCategory::ServerError, // Should never happen
        }
    }

    /// Get the canonical reason phrase for this status code
    pub fn reason_phrase(&self) -> &'static str {
        match self {
            StatusCode::Continue => "Continue",
            StatusCode::SwitchingProtocols => "Switching Protocols",
            StatusCode::Processing => "Processing",
            StatusCode::EarlyHints => "Early Hints",

            StatusCode::Ok => "OK",
            StatusCode::Created => "Created",
            StatusCode::Accepted => "Accepted",
            StatusCode::NonAuthoritativeInformation => "Non-Authoritative Information",
            StatusCode::NoContent => "No Content",
            StatusCode::ResetContent => "Reset Content",
            StatusCode::PartialContent => "Partial Content",
            StatusCode::MultiStatus => "Multi-Status",
            StatusCode::AlreadyReported => "Already Reported",
            StatusCode::ImUsed => "IM Used",

            StatusCode::MultipleChoices => "Multiple Choices",
            StatusCode::MovedPermanently => "Moved Permanently",
            StatusCode::Found => "Found",
            StatusCode::SeeOther => "See Other",
            StatusCode::NotModified => "Not Modified",
            StatusCode::UseProxy => "Use Proxy",
            StatusCode::TemporaryRedirect => "Temporary Redirect",
            StatusCode::PermanentRedirect => "Permanent Redirect",

            StatusCode::BadRequest => "Bad Request",
            StatusCode::Unauthorized => "Unauthorized",
            StatusCode::PaymentRequired => "Payment Required",
            StatusCode::Forbidden => "Forbidden",
            StatusCode::NotFound => "Not Found",
            StatusCode::MethodNotAllowed => "Method Not Allowed",
            StatusCode::NotAcceptable => "Not Acceptable",
            StatusCode::ProxyAuthenticationRequired => "Proxy Authentication Required",
            StatusCode::RequestTimeout => "Request Timeout",
            StatusCode::Conflict => "Conflict",
            StatusCode::Gone => "Gone",
            StatusCode::LengthRequired => "Length Required",
            StatusCode::PreconditionFailed => "Precondition Failed",
            StatusCode::PayloadTooLarge => "Payload Too Large",
            StatusCode::UriTooLong => "URI Too Long",
            StatusCode::UnsupportedMediaType => "Unsupported Media Type",
            StatusCode::RangeNotSatisfiable => "Range Not Satisfiable",
            StatusCode::ExpectationFailed => "Expectation Failed",
            StatusCode::ImATeapot => "I'm a teapot",
            StatusCode::MisdirectedRequest => "Misdirected Request",
            StatusCode::UnprocessableEntity => "Unprocessable Entity",
            StatusCode::Locked => "Locked",
            StatusCode::FailedDependency => "Failed Dependency",
            StatusCode::TooEarly => "Too Early",
            StatusCode::UpgradeRequired => "Upgrade Required",
            StatusCode::PreconditionRequired => "Precondition Required",
            StatusCode::TooManyRequests => "Too Many Requests",
            StatusCode::RequestHeaderFieldsTooLarge => "Request Header Fields Too Large",
            StatusCode::UnavailableForLegalReasons => "Unavailable For Legal Reasons",

            StatusCode::InternalServerError => "Internal Server Error",
            StatusCode::NotImplemented => "Not Implemented",
            StatusCode::BadGateway => "Bad Gateway",
            StatusCode::ServiceUnavailable => "Service Unavailable",
            StatusCode::GatewayTimeout => "Gateway Timeout",
            StatusCode::HttpVersionNotSupported => "HTTP Version Not Supported",
            StatusCode::VariantAlsoNegotiates => "Variant Also Negotiates",
            StatusCode::InsufficientStorage => "Insufficient Storage",
            StatusCode::LoopDetected => "Loop Detected",
            StatusCode::NotExtended => "Not Extended",
            StatusCode::NetworkAuthenticationRequired => "Network Authentication Required",
        }
    }

    /// Check if this is a successful status code (2xx)
    pub fn is_success(&self) -> bool {
        matches!(self.category(), StatusCodeCategory::Success)
    }

    /// Check if this is a redirection status code (3xx)
    pub fn is_redirection(&self) -> bool {
        matches!(self.category(), StatusCodeCategory::Redirection)
    }

    /// Check if this is a client error status code (4xx)
    pub fn is_client_error(&self) -> bool {
        matches!(self.category(), StatusCodeCategory::ClientError)
    }

    /// Check if this is a server error status code (5xx)
    pub fn is_server_error(&self) -> bool {
        matches!(self.category(), StatusCodeCategory::ServerError)
    }

    /// Check if this is an error status code (4xx or 5xx)
    pub fn is_error(&self) -> bool {
        self.is_client_error() || self.is_server_error()
    }

    /// Parse status code from u16
    pub fn from_u16(code: u16) -> Option<Self> {
        match code {
            100 => Some(StatusCode::Continue),
            101 => Some(StatusCode::SwitchingProtocols),
            102 => Some(StatusCode::Processing),
            103 => Some(StatusCode::EarlyHints),

            200 => Some(StatusCode::Ok),
            201 => Some(StatusCode::Created),
            202 => Some(StatusCode::Accepted),
            203 => Some(StatusCode::NonAuthoritativeInformation),
            204 => Some(StatusCode::NoContent),
            205 => Some(StatusCode::ResetContent),
            206 => Some(StatusCode::PartialContent),
            207 => Some(StatusCode::MultiStatus),
            208 => Some(StatusCode::AlreadyReported),
            226 => Some(StatusCode::ImUsed),

            300 => Some(StatusCode::MultipleChoices),
            301 => Some(StatusCode::MovedPermanently),
            302 => Some(StatusCode::Found),
            303 => Some(StatusCode::SeeOther),
            304 => Some(StatusCode::NotModified),
            305 => Some(StatusCode::UseProxy),
            307 => Some(StatusCode::TemporaryRedirect),
            308 => Some(StatusCode::PermanentRedirect),

            400 => Some(StatusCode::BadRequest),
            401 => Some(StatusCode::Unauthorized),
            402 => Some(StatusCode::PaymentRequired),
            403 => Some(StatusCode::Forbidden),
            404 => Some(StatusCode::NotFound),
            405 => Some(StatusCode::MethodNotAllowed),
            406 => Some(StatusCode::NotAcceptable),
            407 => Some(StatusCode::ProxyAuthenticationRequired),
            408 => Some(StatusCode::RequestTimeout),
            409 => Some(StatusCode::Conflict),
            410 => Some(StatusCode::Gone),
            411 => Some(StatusCode::LengthRequired),
            412 => Some(StatusCode::PreconditionFailed),
            413 => Some(StatusCode::PayloadTooLarge),
            414 => Some(StatusCode::UriTooLong),
            415 => Some(StatusCode::UnsupportedMediaType),
            416 => Some(StatusCode::RangeNotSatisfiable),
            417 => Some(StatusCode::ExpectationFailed),
            418 => Some(StatusCode::ImATeapot),
            421 => Some(StatusCode::MisdirectedRequest),
            422 => Some(StatusCode::UnprocessableEntity),
            423 => Some(StatusCode::Locked),
            424 => Some(StatusCode::FailedDependency),
            425 => Some(StatusCode::TooEarly),
            426 => Some(StatusCode::UpgradeRequired),
            428 => Some(StatusCode::PreconditionRequired),
            429 => Some(StatusCode::TooManyRequests),
            431 => Some(StatusCode::RequestHeaderFieldsTooLarge),
            451 => Some(StatusCode::UnavailableForLegalReasons),

            500 => Some(StatusCode::InternalServerError),
            501 => Some(StatusCode::NotImplemented),
            502 => Some(StatusCode::BadGateway),
            503 => Some(StatusCode::ServiceUnavailable),
            504 => Some(StatusCode::GatewayTimeout),
            505 => Some(StatusCode::HttpVersionNotSupported),
            506 => Some(StatusCode::VariantAlsoNegotiates),
            507 => Some(StatusCode::InsufficientStorage),
            508 => Some(StatusCode::LoopDetected),
            510 => Some(StatusCode::NotExtended),
            511 => Some(StatusCode::NetworkAuthenticationRequired),

            _ => None,
        }
    }
}

impl Default for StatusCode {
    fn default() -> Self {
        StatusCode::Ok
    }
}

impl std::fmt::Display for StatusCode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {}", self.as_u16(), self.reason_phrase())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_status_code_values() {
        assert_eq!(StatusCode::Ok.as_u16(), 200);
        assert_eq!(StatusCode::NotFound.as_u16(), 404);
        assert_eq!(StatusCode::InternalServerError.as_u16(), 500);
    }

    #[test]
    fn test_status_code_categories() {
        assert!(matches!(
            StatusCode::Ok.category(),
            StatusCodeCategory::Success
        ));
        assert!(matches!(
            StatusCode::NotFound.category(),
            StatusCodeCategory::ClientError
        ));
        assert!(matches!(
            StatusCode::InternalServerError.category(),
            StatusCodeCategory::ServerError
        ));
        assert!(matches!(
            StatusCode::MovedPermanently.category(),
            StatusCodeCategory::Redirection
        ));
        assert!(matches!(
            StatusCode::Continue.category(),
            StatusCodeCategory::Informational
        ));
    }

    #[test]
    fn test_status_code_predicates() {
        assert!(StatusCode::Ok.is_success());
        assert!(!StatusCode::NotFound.is_success());

        assert!(StatusCode::NotFound.is_client_error());
        assert!(StatusCode::InternalServerError.is_server_error());

        assert!(StatusCode::NotFound.is_error());
        assert!(StatusCode::InternalServerError.is_error());
        assert!(!StatusCode::Ok.is_error());
    }

    #[test]
    fn test_reason_phrases() {
        assert_eq!(StatusCode::Ok.reason_phrase(), "OK");
        assert_eq!(StatusCode::NotFound.reason_phrase(), "Not Found");
        assert_eq!(
            StatusCode::InternalServerError.reason_phrase(),
            "Internal Server Error"
        );
    }

    #[test]
    fn test_from_u16() {
        assert_eq!(StatusCode::from_u16(200), Some(StatusCode::Ok));
        assert_eq!(StatusCode::from_u16(404), Some(StatusCode::NotFound));
        assert_eq!(StatusCode::from_u16(999), None);
    }

    #[test]
    fn test_display() {
        assert_eq!(StatusCode::Ok.to_string(), "200 OK");
        assert_eq!(StatusCode::NotFound.to_string(), "404 Not Found");
    }
}
