//! Minimal DAP protocol types
//!
//! Implements essential Debug Adapter Protocol messages.

use serde::{Deserialize, Serialize};
use serde_json::Value;

/// DAP message envelope
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum Message {
    #[serde(rename = "request")]
    Request(RequestMessage),
    #[serde(rename = "response")]
    Response(ResponseMessage),
    #[serde(rename = "event")]
    Event(EventMessage),
}

/// Request message from client
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RequestMessage {
    pub seq: i64,
    pub command: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub arguments: Option<Value>,
}

/// Response message to client
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResponseMessage {
    pub seq: i64,
    pub request_seq: i64,
    pub success: bool,
    pub command: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub message: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub body: Option<Value>,
}

/// Event message (server to client notification)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EventMessage {
    pub seq: i64,
    pub event: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub body: Option<Value>,
}

/// Initialize request arguments
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct InitializeRequestArguments {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub client_id: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub adapter_id: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub lines_start_at1: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub columns_start_at1: Option<bool>,
}

/// Capabilities response
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
#[serde(rename_all = "camelCase")]
pub struct Capabilities {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub supports_configuration_done_request: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub supports_breakpoint_locations_request: Option<bool>,
}

/// Launch request arguments
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LaunchRequestArguments {
    pub program: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub args: Option<Vec<String>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub cwd: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub stop_on_entry: Option<bool>,
}

/// Breakpoint location
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SourceBreakpoint {
    pub line: i64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub column: Option<i64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub condition: Option<String>,
}

/// Set breakpoints request arguments
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SetBreakpointsArguments {
    pub source: Source,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub breakpoints: Option<Vec<SourceBreakpoint>>,
}

/// Source reference
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Source {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub path: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
}

/// Breakpoint (response)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Breakpoint {
    pub verified: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub line: Option<i64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub message: Option<String>,
}

/// Set breakpoints response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SetBreakpointsResponseBody {
    pub breakpoints: Vec<Breakpoint>,
}

/// Thread info
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Thread {
    pub id: i64,
    pub name: String,
}

/// Threads response body
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ThreadsResponseBody {
    pub threads: Vec<Thread>,
}

/// Stack frame
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct StackFrame {
    pub id: i64,
    pub name: String,
    pub source: Option<Source>,
    pub line: i64,
    pub column: i64,
}

/// Stack trace request arguments
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct StackTraceArguments {
    pub thread_id: i64,
}

/// Stack trace response body
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct StackTraceResponseBody {
    pub stack_frames: Vec<StackFrame>,
}

/// Scope (local, global, etc.)
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Scope {
    pub name: String,
    pub variables_reference: i64,
    pub expensive: bool,
}

/// Scopes request arguments
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ScopesArguments {
    pub frame_id: i64,
}

/// Scopes response body
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ScopesResponseBody {
    pub scopes: Vec<Scope>,
}

/// Variable
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Variable {
    pub name: String,
    pub value: String,
    #[serde(rename = "type")]
    #[serde(skip_serializing_if = "Option::is_none")]
    pub var_type: Option<String>,
    pub variables_reference: i64,
}

/// Variables request arguments
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct VariablesArguments {
    pub variables_reference: i64,
}

/// Variables response body
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VariablesResponseBody {
    pub variables: Vec<Variable>,
}

/// Continue request arguments
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ContinueArguments {
    pub thread_id: i64,
}

/// Step request arguments (next, stepIn, stepOut)
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct StepArguments {
    pub thread_id: i64,
}

/// Stopped event body
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct StoppedEventBody {
    pub reason: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub thread_id: Option<i64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub text: Option<String>,
}

/// Terminated event body
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TerminatedEventBody {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub restart: Option<bool>,
}
