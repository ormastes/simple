//! Minimal LSP protocol types
//!
//! Implements only the essential LSP messages for a working server.

use serde::{Deserialize, Serialize};
use serde_json::Value;

/// LSP message envelope
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(untagged)]
pub enum Message {
    Request(RequestMessage),
    Response(ResponseMessage),
    Notification(NotificationMessage),
}

/// Request message from client
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RequestMessage {
    pub jsonrpc: String,
    pub id: RequestId,
    pub method: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub params: Option<Value>,
}

/// Response message to client
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResponseMessage {
    pub jsonrpc: String,
    pub id: RequestId,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub result: Option<Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<ResponseError>,
}

/// Notification message (no response expected)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NotificationMessage {
    pub jsonrpc: String,
    pub method: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub params: Option<Value>,
}

/// Request ID (can be string or number)
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
#[serde(untagged)]
pub enum RequestId {
    Number(i64),
    String(String),
}

/// Error in response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResponseError {
    pub code: i32,
    pub message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub data: Option<Value>,
}

/// Initialize request parameters
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct InitializeParams {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub process_id: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub root_uri: Option<String>,
    pub capabilities: ClientCapabilities,
}

/// Client capabilities (minimal)
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
#[serde(rename_all = "camelCase")]
pub struct ClientCapabilities {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub text_document: Option<TextDocumentClientCapabilities>,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
#[serde(rename_all = "camelCase")]
pub struct TextDocumentClientCapabilities {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub synchronization: Option<Value>,
}

/// Initialize result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InitializeResult {
    pub capabilities: ServerCapabilities,
}

/// Server capabilities (minimal)
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
#[serde(rename_all = "camelCase")]
pub struct ServerCapabilities {
    /// Text document sync kind: 1 = Full
    #[serde(skip_serializing_if = "Option::is_none")]
    pub text_document_sync: Option<i32>,
}

/// Text document identifier
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TextDocumentIdentifier {
    pub uri: String,
}

/// Text document item
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TextDocumentItem {
    pub uri: String,
    pub language_id: String,
    pub version: i32,
    pub text: String,
}

/// Did open text document params
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct DidOpenTextDocumentParams {
    pub text_document: TextDocumentItem,
}

/// Did change text document params
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct DidChangeTextDocumentParams {
    pub text_document: VersionedTextDocumentIdentifier,
    pub content_changes: Vec<TextDocumentContentChangeEvent>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VersionedTextDocumentIdentifier {
    pub uri: String,
    pub version: i32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TextDocumentContentChangeEvent {
    pub text: String,
}

/// Diagnostic (error/warning)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Diagnostic {
    pub range: Range,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub severity: Option<DiagnosticSeverity>,
    pub message: String,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum DiagnosticSeverity {
    Error = 1,
    Warning = 2,
    Information = 3,
    Hint = 4,
}

/// Position in text document
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub struct Position {
    pub line: u32,
    pub character: u32,
}

/// Range in text document
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub struct Range {
    pub start: Position,
    pub end: Position,
}

/// Publish diagnostics params
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PublishDiagnosticsParams {
    pub uri: String,
    pub diagnostics: Vec<Diagnostic>,
}
