//! LSP server implementation
//!
//! Minimal server supporting:
//! - Initialize/shutdown lifecycle
//! - Text document synchronization
//! - Parse error diagnostics

use crate::protocol::*;
use crate::transport::{read_message, write_message, TransportError};
use simple_parser::Parser;
use std::collections::HashMap;
use std::io::{self, BufReader, BufWriter};

/// LSP server state
pub struct LspServer {
    /// Open documents
    documents: HashMap<String, String>,
    /// Whether server is initialized
    initialized: bool,
    /// Whether shutdown was requested
    shutdown_requested: bool,
}

impl LspServer {
    /// Create new LSP server
    pub fn new() -> Self {
        Self {
            documents: HashMap::new(),
            initialized: false,
            shutdown_requested: false,
        }
    }

    /// Run the server (blocking)
    pub fn run(&mut self) -> Result<(), TransportError> {
        let stdin = io::stdin();
        let stdout = io::stdout();
        let mut reader = BufReader::new(stdin);
        let mut writer = BufWriter::new(stdout);

        loop {
            let message = read_message(&mut reader)?;

            match message {
                Message::Request(req) => {
                    if let Some(response) = self.handle_request(&req) {
                        write_message(&mut writer, &Message::Response(response))?;
                    }

                    // Exit after shutdown
                    if self.shutdown_requested && req.method == "shutdown" {
                        // Wait for exit notification
                        continue;
                    }
                }
                Message::Notification(notif) => {
                    self.handle_notification(&notif, &mut writer)?;

                    // Exit on exit notification
                    if notif.method == "exit" {
                        break;
                    }
                }
                Message::Response(_) => {
                    // Ignore responses (we don't send requests)
                }
            }
        }

        Ok(())
    }

    /// Handle request message
    fn handle_request(&mut self, req: &RequestMessage) -> Option<ResponseMessage> {
        let result = match req.method.as_str() {
            "initialize" => self.handle_initialize(req),
            "shutdown" => self.handle_shutdown(req),
            _ => {
                // Unknown method
                Some(ResponseMessage {
                    jsonrpc: "2.0".to_string(),
                    id: req.id.clone(),
                    result: None,
                    error: Some(ResponseError {
                        code: -32601,
                        message: format!("Method not found: {}", req.method),
                        data: None,
                    }),
                })
            }
        };

        result
    }

    /// Handle notification message
    fn handle_notification<W: io::Write>(
        &mut self,
        notif: &NotificationMessage,
        writer: &mut W,
    ) -> Result<(), TransportError> {
        match notif.method.as_str() {
            "initialized" => {
                self.initialized = true;
            }
            "textDocument/didOpen" => {
                self.handle_did_open(notif, writer)?;
            }
            "textDocument/didChange" => {
                self.handle_did_change(notif, writer)?;
            }
            "exit" => {
                // Will be handled by caller
            }
            _ => {
                // Ignore unknown notifications
            }
        }

        Ok(())
    }

    /// Handle initialize request
    fn handle_initialize(&mut self, req: &RequestMessage) -> Option<ResponseMessage> {
        let result = InitializeResult {
            capabilities: ServerCapabilities {
                text_document_sync: Some(1), // Full sync
            },
        };

        Some(ResponseMessage {
            jsonrpc: "2.0".to_string(),
            id: req.id.clone(),
            result: serde_json::to_value(&result).ok(),
            error: None,
        })
    }

    /// Handle shutdown request
    fn handle_shutdown(&mut self, req: &RequestMessage) -> Option<ResponseMessage> {
        self.shutdown_requested = true;

        Some(ResponseMessage {
            jsonrpc: "2.0".to_string(),
            id: req.id.clone(),
            result: Some(serde_json::Value::Null),
            error: None,
        })
    }

    /// Handle didOpen notification
    fn handle_did_open<W: io::Write>(
        &mut self,
        notif: &NotificationMessage,
        writer: &mut W,
    ) -> Result<(), TransportError> {
        let params: DidOpenTextDocumentParams = serde_json::from_value(
            notif.params.clone().unwrap_or_default()
        ).unwrap_or_else(|_| {
            panic!("Invalid didOpen params");
        });

        let uri = params.text_document.uri.clone();
        let text = params.text_document.text.clone();

        self.documents.insert(uri.clone(), text.clone());

        // Parse and send diagnostics
        self.send_diagnostics(&uri, &text, writer)?;

        Ok(())
    }

    /// Handle didChange notification
    fn handle_did_change<W: io::Write>(
        &mut self,
        notif: &NotificationMessage,
        writer: &mut W,
    ) -> Result<(), TransportError> {
        let params: DidChangeTextDocumentParams = serde_json::from_value(
            notif.params.clone().unwrap_or_default()
        ).unwrap_or_else(|_| {
            panic!("Invalid didChange params");
        });

        let uri = params.text_document.uri.clone();

        // Full sync: take the new text
        if let Some(change) = params.content_changes.first() {
            let text = change.text.clone();
            self.documents.insert(uri.clone(), text.clone());

            // Parse and send diagnostics
            self.send_diagnostics(&uri, &text, writer)?;
        }

        Ok(())
    }

    /// Parse document and send diagnostics
    fn send_diagnostics<W: io::Write>(
        &self,
        uri: &str,
        text: &str,
        writer: &mut W,
    ) -> Result<(), TransportError> {
        let mut diagnostics = Vec::new();

        // Parse the document
        let mut parser = Parser::new(text);
        match parser.parse() {
            Ok(_) => {
                // No errors
            }
            Err(err) => {
                // Convert parse error to diagnostic
                let error_message = err.to_string();
                let span = err.span().unwrap_or_else(|| simple_parser::token::Span::new(0, 1, 1, 1));

                let diagnostic = Diagnostic {
                    range: Range {
                        start: Position {
                            line: (span.line as u32).saturating_sub(1),
                            character: (span.column as u32).saturating_sub(1),
                        },
                        end: Position {
                            line: (span.line as u32).saturating_sub(1),
                            character: (span.column as u32).saturating_sub(1) + (span.end - span.start) as u32,
                        },
                    },
                    severity: Some(DiagnosticSeverity::Error),
                    message: error_message,
                };
                diagnostics.push(diagnostic);
            }
        }

        // Send diagnostics
        let params = PublishDiagnosticsParams {
            uri: uri.to_string(),
            diagnostics,
        };

        let notification = NotificationMessage {
            jsonrpc: "2.0".to_string(),
            method: "textDocument/publishDiagnostics".to_string(),
            params: serde_json::to_value(&params).ok(),
        };

        write_message(writer, &Message::Notification(notification))?;

        Ok(())
    }
}

impl Default for LspServer {
    fn default() -> Self {
        Self::new()
    }
}
