use std::collections::HashSet;
use std::io::{BufRead, BufReader, Read, Write};
use std::process::{Command, Stdio};

fn send_msg(stdin: &mut impl Write, obj: &str) -> Result<(), String> {
    let body = obj.as_bytes();
    let header = format!("Content-Length: {}\r\n\r\n", body.len());
    stdin
        .write_all(header.as_bytes())
        .map_err(|e| format!("write header failed: {e}"))?;
    stdin
        .write_all(body)
        .map_err(|e| format!("write body failed: {e}"))?;
    stdin.flush().map_err(|e| format!("flush failed: {e}"))?;
    Ok(())
}

fn read_msg(reader: &mut BufReader<impl Read>) -> Result<String, String> {
    let mut headers: Vec<String> = Vec::new();
    loop {
        let mut line = String::new();
        let n = reader
            .read_line(&mut line)
            .map_err(|e| format!("read header failed: {e}"))?;
        if n == 0 {
            return Err("EOF while reading header".to_string());
        }
        if line == "\r\n" || line == "\n" {
            break;
        }
        headers.push(line);
    }
    let mut content_len: Option<usize> = None;
    for h in headers {
        let lower = h.to_ascii_lowercase();
        if let Some(rest) = lower.strip_prefix("content-length:") {
            content_len = rest.trim().parse::<usize>().ok();
            break;
        }
    }
    let len = content_len.ok_or("missing content-length".to_string())?;
    let mut body = vec![0u8; len];
    reader
        .read_exact(&mut body)
        .map_err(|e| format!("read body failed: {e}"))?;
    String::from_utf8(body).map_err(|e| format!("utf8 parse failed: {e}"))
}

fn extract_json_string(body: &str, key: &str) -> Option<String> {
    let pat = format!("\"{key}\":\"");
    let start = body.find(&pat)? + pat.len();
    let tail = &body[start..];
    let end = tail.find('"')?;
    Some(tail[..end].to_string())
}

fn extract_session_id(body: &str) -> Option<String> {
    let prefix = "session_";
    let mut seek = body;
    while let Some(pos) = seek.find(prefix) {
        let tail = &seek[pos + prefix.len()..];
        let mut digits = String::new();
        for ch in tail.chars() {
            if ch.is_ascii_digit() {
                digits.push(ch);
            } else {
                break;
            }
        }
        if !digits.is_empty() {
            return Some(format!("{prefix}{digits}"));
        }
        seek = &tail[1..];
    }
    None
}

fn assert_ok(cond: bool, msg: &str) -> Result<(), String> {
    if cond {
        Ok(())
    } else {
        Err(msg.to_string())
    }
}

fn run() -> Result<(), String> {
    let mut child = Command::new("bin/simple_mcp_server")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .map_err(|e| format!("spawn failed: {e}"))?;
    let mut stdin = child.stdin.take().ok_or("missing child stdin".to_string())?;
    let stdout = child.stdout.take().ok_or("missing child stdout".to_string())?;
    let mut reader = BufReader::new(stdout);

    send_msg(
        &mut stdin,
        r#"{"jsonrpc":"2.0","id":"1","method":"initialize","params":{"protocolVersion":"2025-06-18","capabilities":{},"clientInfo":{"name":"probe-rust","version":"1.0"}}}"#,
    )?;
    let init_resp = read_msg(&mut reader)?;
    assert_ok(init_resp.contains("\"result\""), "initialize failed")?;

    send_msg(&mut stdin, r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#)?;

    send_msg(&mut stdin, r#"{"jsonrpc":"2.0","id":"2","method":"tools/list","params":{}}"#)?;
    let tools_resp = read_msg(&mut reader)?;
    let mut names = HashSet::new();
    let mut seek = tools_resp.as_str();
    let tag = "\"name\":\"";
    while let Some(pos) = seek.find(tag) {
        let rem = &seek[pos + tag.len()..];
        if let Some(end) = rem.find('"') {
            names.insert(rem[..end].to_string());
            seek = &rem[end + 1..];
        } else {
            break;
        }
    }
    assert_ok(names.contains("debug_create_session"), "debug_create_session missing from tools/list")?;
    assert_ok(names.contains("debug_log_status"), "debug_log_status missing from tools/list")?;

    send_msg(
        &mut stdin,
        r#"{"jsonrpc":"2.0","id":"3","method":"tools/call","params":{"name":"debug_create_session","arguments":{"program":"src/app/mcp/main.spl"}}}"#,
    )?;
    let create_resp = read_msg(&mut reader)?;
    let session_id = extract_json_string(&create_resp, "session_id")
        .or_else(|| extract_session_id(&create_resp))
        .ok_or("missing session_id".to_string())?;
    assert_ok(!session_id.is_empty(), "debug_create_session empty session_id")?;

    send_msg(
        &mut stdin,
        r#"{"jsonrpc":"2.0","id":"4","method":"tools/call","params":{"name":"debug_list_sessions","arguments":{}}}"#,
    )?;
    let list_resp = read_msg(&mut reader)?;
    assert_ok(
        list_resp.contains(&session_id),
        "debug_list_sessions did not include created session",
    )?;

    send_msg(
        &mut stdin,
        r#"{"jsonrpc":"2.0","id":"5","method":"tools/call","params":{"name":"debug_log_enable","arguments":{"pattern":"*"}}}"#,
    )?;
    let enable_resp = read_msg(&mut reader)?;
    assert_ok(
        enable_resp.contains("enabled"),
        "debug_log_enable did not enable logging",
    )?;

    send_msg(
        &mut stdin,
        r#"{"jsonrpc":"2.0","id":"6","method":"tools/call","params":{"name":"debug_log_status","arguments":{}}}"#,
    )?;
    let status_resp = read_msg(&mut reader)?;
    assert_ok(
        status_resp.contains("enabled") && status_resp.contains(":true"),
        "debug_log_status did not report enabled=true",
    )?;

    println!("rust probe: OK (session={session_id})");

    send_msg(&mut stdin, r#"{"jsonrpc":"2.0","id":"7","method":"shutdown","params":{}}"#)?;
    let _ = read_msg(&mut reader)?;
    let _ = child.kill();
    Ok(())
}

fn main() {
    if let Err(err) = run() {
        eprintln!("rust probe: FAIL - {err}");
        std::process::exit(1);
    }
}
