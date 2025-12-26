//! Integration tests for Simple DAP server

use serde_json::json;
use std::io::{BufRead, BufReader, Write};
use std::process::{Command, Stdio};

/// Helper to send a DAP message
fn send_message(stdin: &mut impl Write, seq: i64, command: &str, arguments: Option<serde_json::Value>) {
    let message = json!({
        "type": "request",
        "seq": seq,
        "command": command,
        "arguments": arguments
    });

    let content = serde_json::to_string(&message).unwrap();
    let header = format!("Content-Length: {}\r\n\r\n", content.len());

    stdin.write_all(header.as_bytes()).unwrap();
    stdin.write_all(content.as_bytes()).unwrap();
    stdin.flush().unwrap();
}

/// Helper to read a DAP message
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
fn test_dap_initialize() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_simple-dap"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("Failed to start DAP server");

    let mut stdin = child.stdin.take().unwrap();
    let stdout = child.stdout.take().unwrap();
    let mut reader = BufReader::new(stdout);

    // Send initialize request
    send_message(
        &mut stdin,
        1,
        "initialize",
        Some(json!({
            "clientID": "test",
            "adapterID": "simple",
            "linesStartAt1": true,
            "columnsStartAt1": true
        })),
    );

    // Read initialize response
    let response = read_message(&mut reader).expect("Failed to read initialize response");

    assert_eq!(response["type"], "response");
    assert_eq!(response["command"], "initialize");
    assert_eq!(response["success"], true);
    assert!(response["body"]["supportsConfigurationDoneRequest"].as_bool().unwrap_or(false));

    // Send disconnect
    send_message(&mut stdin, 2, "disconnect", None);

    // Read disconnect response
    let _ = read_message(&mut reader);

    let _ = child.wait();
}

#[test]
fn test_dap_breakpoints() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_simple-dap"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("Failed to start DAP server");

    let mut stdin = child.stdin.take().unwrap();
    let stdout = child.stdout.take().unwrap();
    let mut reader = BufReader::new(stdout);

    // Initialize
    send_message(&mut stdin, 1, "initialize", Some(json!({})));
    let _ = read_message(&mut reader);

    // Launch
    send_message(
        &mut stdin,
        2,
        "launch",
        Some(json!({
            "program": "test.spl",
            "stopOnEntry": false
        })),
    );
    let _ = read_message(&mut reader); // launch response
    let _ = read_message(&mut reader); // initialized event

    // Set breakpoints
    send_message(
        &mut stdin,
        3,
        "setBreakpoints",
        Some(json!({
            "source": {
                "path": "test.spl"
            },
            "breakpoints": [
                { "line": 10 },
                { "line": 20 }
            ]
        })),
    );

    // Read setBreakpoints response
    let response = read_message(&mut reader).expect("Failed to read setBreakpoints response");

    assert_eq!(response["type"], "response");
    assert_eq!(response["command"], "setBreakpoints");
    assert_eq!(response["success"], true);

    let breakpoints = &response["body"]["breakpoints"];
    assert!(breakpoints.is_array());
    assert_eq!(breakpoints.as_array().unwrap().len(), 2);
    assert_eq!(breakpoints[0]["verified"], true);
    assert_eq!(breakpoints[0]["line"], 10);

    // Disconnect
    send_message(&mut stdin, 4, "disconnect", None);
    let _ = read_message(&mut reader);

    let _ = child.wait();
}

#[test]
fn test_dap_threads_and_stack() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_simple-dap"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("Failed to start DAP server");

    let mut stdin = child.stdin.take().unwrap();
    let stdout = child.stdout.take().unwrap();
    let mut reader = BufReader::new(stdout);

    // Initialize
    send_message(&mut stdin, 1, "initialize", Some(json!({})));
    let _ = read_message(&mut reader);

    // Launch with stopOnEntry
    send_message(
        &mut stdin,
        2,
        "launch",
        Some(json!({
            "program": "test.spl",
            "stopOnEntry": true
        })),
    );
    let _ = read_message(&mut reader); // launch response
    let _ = read_message(&mut reader); // initialized event

    // Get threads
    send_message(&mut stdin, 3, "threads", None);
    let response = read_message(&mut reader).expect("Failed to read threads response");

    assert_eq!(response["command"], "threads");
    assert_eq!(response["success"], true);
    let threads = &response["body"]["threads"];
    assert!(threads.is_array());
    assert!(threads.as_array().unwrap().len() > 0);

    // Get stack trace
    send_message(
        &mut stdin,
        4,
        "stackTrace",
        Some(json!({ "threadId": 1 })),
    );
    let response = read_message(&mut reader).expect("Failed to read stackTrace response");

    assert_eq!(response["command"], "stackTrace");
    assert_eq!(response["success"], true);
    let frames = &response["body"]["stackFrames"];
    assert!(frames.is_array());

    // Disconnect
    send_message(&mut stdin, 5, "disconnect", None);
    let _ = read_message(&mut reader);

    let _ = child.wait();
}
