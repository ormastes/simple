//! Integration tests for Simple LSP server

use serde_json::json;
use std::io::{BufRead, BufReader, Write};
use std::process::{Command, Stdio};

/// Helper to send a JSON-RPC message to the LSP server
fn send_message(stdin: &mut impl Write, method: &str, id: Option<i64>, params: serde_json::Value) {
    let message = if let Some(id) = id {
        json!({
            "jsonrpc": "2.0",
            "id": id,
            "method": method,
            "params": params
        })
    } else {
        json!({
            "jsonrpc": "2.0",
            "method": method,
            "params": params
        })
    };

    let content = serde_json::to_string(&message).unwrap();
    let header = format!("Content-Length: {}\r\n\r\n", content.len());

    stdin.write_all(header.as_bytes()).unwrap();
    stdin.write_all(content.as_bytes()).unwrap();
    stdin.flush().unwrap();
}

/// Helper to read a JSON-RPC message from the LSP server
fn read_message<R: BufRead>(reader: &mut R) -> Option<serde_json::Value> {
    let mut content_length: Option<usize> = None;

    // Read headers
    loop {
        let mut line = String::new();
        if reader.read_line(&mut line).unwrap() == 0 {
            return None;
        }

        let line = line.trim();
        if line.is_empty() {
            break;
        }

        if let Some(value) = line.strip_prefix("Content-Length: ") {
            content_length = Some(value.parse().unwrap());
        }
    }

    let content_length = content_length?;

    // Read content
    let mut buffer = vec![0u8; content_length];
    reader.read_exact(&mut buffer).ok()?;

    serde_json::from_slice(&buffer).ok()
}

#[test]
fn test_lsp_initialize() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_simple-lsp"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("Failed to start LSP server");

    let mut stdin = child.stdin.take().unwrap();
    let stdout = child.stdout.take().unwrap();
    let mut reader = BufReader::new(stdout);

    // Send initialize request
    send_message(
        &mut stdin,
        "initialize",
        Some(1),
        json!({
            "processId": null,
            "rootUri": null,
            "capabilities": {}
        }),
    );

    // Read initialize response
    let response = read_message(&mut reader).expect("Failed to read initialize response");

    assert_eq!(response["jsonrpc"], "2.0");
    assert_eq!(response["id"], 1);
    assert!(response["result"]["capabilities"]["textDocumentSync"].is_number());

    // Send initialized notification
    send_message(&mut stdin, "initialized", None, json!({}));

    // Send shutdown request
    send_message(&mut stdin, "shutdown", Some(2), json!(null));

    // Read shutdown response
    let response = read_message(&mut reader).expect("Failed to read shutdown response");
    assert_eq!(response["id"], 2);

    // Send exit notification
    send_message(&mut stdin, "exit", None, json!(null));

    // Wait for server to exit
    let status = child.wait().unwrap();
    assert!(status.success() || status.code() == Some(0));
}

#[test]
fn test_lsp_diagnostics() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_simple-lsp"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("Failed to start LSP server");

    let mut stdin = child.stdin.take().unwrap();
    let stdout = child.stdout.take().unwrap();
    let mut reader = BufReader::new(stdout);

    // Initialize
    send_message(
        &mut stdin,
        "initialize",
        Some(1),
        json!({
            "processId": null,
            "rootUri": null,
            "capabilities": {}
        }),
    );
    let _ = read_message(&mut reader);

    send_message(&mut stdin, "initialized", None, json!({}));

    // Open a document with a syntax error
    send_message(
        &mut stdin,
        "textDocument/didOpen",
        None,
        json!({
            "textDocument": {
                "uri": "file:///test.spl",
                "languageId": "simple",
                "version": 1,
                "text": "fn main(\n    return 0"  // Missing colon after main(
            }
        }),
    );

    // Read diagnostics
    let diagnostics_msg = read_message(&mut reader).expect("Failed to read diagnostics");

    assert_eq!(diagnostics_msg["method"], "textDocument/publishDiagnostics");
    assert_eq!(diagnostics_msg["params"]["uri"], "file:///test.spl");

    let diagnostics = &diagnostics_msg["params"]["diagnostics"];
    assert!(diagnostics.is_array());
    assert!(diagnostics.as_array().unwrap().len() > 0);

    // Shutdown
    send_message(&mut stdin, "shutdown", Some(2), json!(null));
    let _ = read_message(&mut reader);
    send_message(&mut stdin, "exit", None, json!(null));

    let _ = child.wait();
}
