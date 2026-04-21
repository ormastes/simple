use crate::error::CompileError;
use crate::value::Value;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicI64, Ordering};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

static NEXT_REQUEST_ID: AtomicI64 = AtomicI64::new(1);
static NEXT_EVENT_ID: AtomicI64 = AtomicI64::new(1);

#[derive(Default)]
struct BridgeRequest {
    request_id: i64,
    client_id: i64,
    method: i64,
    window_id: i64,
    title: String,
    x: i64,
    y: i64,
    w: i64,
    h: i64,
    content: String,
    process_id: i64,
    app_id: String,
}

fn get_i64(args: &[Value], idx: usize, name: &str) -> Result<i64, CompileError> {
    match args.get(idx) {
        Some(Value::Int(v)) => Ok(*v),
        _ => Err(CompileError::runtime(&format!(
            "{name}: argument {idx} must be an integer"
        ))),
    }
}

fn get_string(args: &[Value], idx: usize, name: &str) -> Result<String, CompileError> {
    match args.get(idx) {
        Some(Value::Str(v)) => Ok(v.clone()),
        _ => Err(CompileError::runtime(&format!(
            "{name}: argument {idx} must be a string"
        ))),
    }
}

fn bridge_dir_from_env() -> Option<PathBuf> {
    std::env::var_os("SIMPLE_HOST_WM_DIR")
        .map(PathBuf::from)
        .filter(|p| !p.as_os_str().is_empty())
}

fn ensure_bridge_dirs(dir: &Path) -> std::io::Result<()> {
    fs::create_dir_all(dir.join("requests"))?;
    fs::create_dir_all(dir.join("replies"))?;
    fs::create_dir_all(dir.join("events"))?;
    Ok(())
}

fn now_nanos() -> u128 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos()
}

fn next_request_id() -> i64 {
    (std::process::id() as i64)
        .saturating_mul(1_000_000_000)
        .saturating_add(NEXT_REQUEST_ID.fetch_add(1, Ordering::Relaxed))
}

fn hex_encode(input: &str) -> String {
    let mut out = String::with_capacity(input.len() * 2);
    for b in input.as_bytes() {
        out.push_str(&format!("{b:02x}"));
    }
    out
}

fn hex_decode(input: &str) -> String {
    let bytes = input.as_bytes();
    let mut out = Vec::with_capacity(bytes.len() / 2);
    let mut i = 0;
    while i + 1 < bytes.len() {
        if let Ok(byte) = u8::from_str_radix(&input[i..i + 2], 16) {
            out.push(byte);
        }
        i += 2;
    }
    String::from_utf8_lossy(&out).to_string()
}

fn parse_kv(content: &str) -> std::collections::HashMap<String, String> {
    let mut map = std::collections::HashMap::new();
    for line in content.lines() {
        if let Some((k, v)) = line.split_once('=') {
            map.insert(k.to_string(), v.to_string());
        }
    }
    map
}

fn read_i64(map: &std::collections::HashMap<String, String>, key: &str) -> i64 {
    map.get(key).and_then(|v| v.parse::<i64>().ok()).unwrap_or(0)
}

fn write_atomic(path: &Path, content: &str) -> std::io::Result<()> {
    let tmp = path.with_extension(format!("tmp.{}.{}", std::process::id(), now_nanos()));
    fs::write(&tmp, content)?;
    fs::rename(tmp, path)?;
    Ok(())
}

fn request_path(dir: &Path, request_id: i64) -> PathBuf {
    dir.join("requests").join(format!("{request_id}.req"))
}

fn reply_path(dir: &Path, request_id: i64) -> PathBuf {
    dir.join("replies").join(format!("{request_id}.rep"))
}

fn parse_request(path: &Path) -> Option<BridgeRequest> {
    let raw = fs::read_to_string(path).ok()?;
    let kv = parse_kv(&raw);
    Some(BridgeRequest {
        request_id: read_i64(&kv, "request_id"),
        client_id: read_i64(&kv, "client_id"),
        method: read_i64(&kv, "method"),
        window_id: read_i64(&kv, "window_id"),
        title: kv.get("title_hex").map(|v| hex_decode(v)).unwrap_or_default(),
        x: read_i64(&kv, "x"),
        y: read_i64(&kv, "y"),
        w: read_i64(&kv, "w"),
        h: read_i64(&kv, "h"),
        content: kv.get("content_hex").map(|v| hex_decode(v)).unwrap_or_default(),
        process_id: read_i64(&kv, "process_id"),
        app_id: kv.get("app_id_hex").map(|v| hex_decode(v)).unwrap_or_default(),
    })
}

pub fn rt_host_wm_server_start(_args: &[Value]) -> Result<Value, CompileError> {
    let dir = std::env::temp_dir().join(format!("simple-host-wm-{}-{}", std::process::id(), now_nanos()));
    ensure_bridge_dirs(&dir).map_err(|e| CompileError::runtime(&format!("rt_host_wm_server_start: {e}")))?;
    Ok(Value::Str(dir.to_string_lossy().to_string()))
}

pub fn rt_host_wm_server_cleanup(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime("rt_host_wm_server_cleanup requires dir"));
    }
    let dir = PathBuf::from(get_string(args, 0, "rt_host_wm_server_cleanup")?);
    let temp_dir = std::env::temp_dir();
    let allowed = dir
        .file_name()
        .and_then(|name| name.to_str())
        .map(|name| name.starts_with("simple-host-wm-"))
        .unwrap_or(false)
        && dir.parent().map(|p| p == temp_dir.as_path()).unwrap_or(false);
    if !allowed {
        return Ok(Value::Bool(false));
    }
    Ok(Value::Bool(fs::remove_dir_all(dir).is_ok()))
}

pub fn serial_println(args: &[Value]) -> Result<Value, CompileError> {
    if let Some(Value::Str(msg)) = args.first() {
        eprintln!("{msg}");
    }
    Ok(Value::Nil)
}

pub fn rt_host_wm_server_poll(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Err(CompileError::runtime("rt_host_wm_server_poll requires dir and max"));
    }
    let dir = PathBuf::from(get_string(args, 0, "rt_host_wm_server_poll")?);
    let max = get_i64(args, 1, "rt_host_wm_server_poll")?.max(0) as usize;
    let req_dir = dir.join("requests");
    let mut paths: Vec<PathBuf> = fs::read_dir(req_dir)
        .ok()
        .into_iter()
        .flat_map(|entries| entries.filter_map(|e| e.ok().map(|e| e.path())))
        .filter(|p| p.extension().and_then(|s| s.to_str()) == Some("req"))
        .collect();
    paths.sort();

    let mut out = Vec::new();
    for path in paths.into_iter().take(max) {
        if let Some(req) = parse_request(&path) {
            out.push(Value::Tuple(vec![
                Value::Int(req.request_id),
                Value::Int(req.client_id),
                Value::Int(req.method),
                Value::Int(req.window_id),
                Value::Str(req.title),
                Value::Int(req.x),
                Value::Int(req.y),
                Value::Int(req.w),
                Value::Int(req.h),
                Value::Str(req.content),
                Value::Int(req.process_id),
                Value::Str(req.app_id),
            ]));
        }
        let _ = fs::remove_file(path);
    }
    Ok(Value::Array(std::sync::Arc::new(out)))
}

pub fn rt_host_wm_server_reply_create(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 4 {
        return Err(CompileError::runtime(
            "rt_host_wm_server_reply_create requires dir, request_id, status, window_id",
        ));
    }
    let dir = PathBuf::from(get_string(args, 0, "rt_host_wm_server_reply_create")?);
    let request_id = get_i64(args, 1, "rt_host_wm_server_reply_create")?;
    let status = get_i64(args, 2, "rt_host_wm_server_reply_create")?;
    let window_id = get_i64(args, 3, "rt_host_wm_server_reply_create")?;
    let content = format!("status={status}\nwindow_id={window_id}\n");
    Ok(Value::Bool(
        write_atomic(&reply_path(&dir, request_id), &content).is_ok(),
    ))
}

pub fn rt_host_wm_server_reply_status(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 3 {
        return Err(CompileError::runtime(
            "rt_host_wm_server_reply_status requires dir, request_id, status",
        ));
    }
    let dir = PathBuf::from(get_string(args, 0, "rt_host_wm_server_reply_status")?);
    let request_id = get_i64(args, 1, "rt_host_wm_server_reply_status")?;
    let status = get_i64(args, 2, "rt_host_wm_server_reply_status")?;
    let content = format!("status={status}\nwindow_id=0\n");
    Ok(Value::Bool(
        write_atomic(&reply_path(&dir, request_id), &content).is_ok(),
    ))
}

pub fn rt_host_wm_server_send_event(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 8 {
        return Err(CompileError::runtime(
            "rt_host_wm_server_send_event requires dir, client_id, window_id, event_type, key, x, y, mods",
        ));
    }
    let dir = PathBuf::from(get_string(args, 0, "rt_host_wm_server_send_event")?);
    let client_id = get_i64(args, 1, "rt_host_wm_server_send_event")?;
    let window_id = get_i64(args, 2, "rt_host_wm_server_send_event")?;
    let event_type = get_i64(args, 3, "rt_host_wm_server_send_event")?;
    let key = get_i64(args, 4, "rt_host_wm_server_send_event")?;
    let x = get_i64(args, 5, "rt_host_wm_server_send_event")?;
    let y = get_i64(args, 6, "rt_host_wm_server_send_event")?;
    let mods = get_i64(args, 7, "rt_host_wm_server_send_event")?;
    let seq = NEXT_EVENT_ID.fetch_add(1, Ordering::Relaxed);
    let path = dir
        .join("events")
        .join(format!("{client_id}_{:020}_{seq}.evt", now_nanos()));
    let content = format!("window_id={window_id}\nevent_type={event_type}\nkey={key}\nx={x}\ny={y}\nmods={mods}\n");
    Ok(Value::Bool(write_atomic(&path, &content).is_ok()))
}

pub fn rt_host_wm_client_connect(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime("rt_host_wm_client_connect requires app_id"));
    }
    if bridge_dir_from_env().is_none() {
        return Ok(Value::Int(0));
    }
    let client_id = std::process::id() as i64;
    Ok(Value::Int(client_id))
}

pub fn rt_host_wm_client_request(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 12 {
        return Err(CompileError::runtime("rt_host_wm_client_request requires 12 arguments"));
    }
    let dir = match bridge_dir_from_env() {
        Some(dir) => dir,
        None => return Ok(Value::Tuple(vec![Value::Int(1), Value::Int(0)])),
    };
    ensure_bridge_dirs(&dir).map_err(|e| CompileError::runtime(&format!("rt_host_wm_client_request: {e}")))?;
    let client_id = get_i64(args, 0, "rt_host_wm_client_request")?;
    let method = get_i64(args, 1, "rt_host_wm_client_request")?;
    let window_id = get_i64(args, 2, "rt_host_wm_client_request")?;
    let title = get_string(args, 3, "rt_host_wm_client_request")?;
    let x = get_i64(args, 4, "rt_host_wm_client_request")?;
    let y = get_i64(args, 5, "rt_host_wm_client_request")?;
    let w = get_i64(args, 6, "rt_host_wm_client_request")?;
    let h = get_i64(args, 7, "rt_host_wm_client_request")?;
    let content = get_string(args, 8, "rt_host_wm_client_request")?;
    let process_id = get_i64(args, 9, "rt_host_wm_client_request")?;
    let app_id = get_string(args, 10, "rt_host_wm_client_request")?;
    let timeout_ms = get_i64(args, 11, "rt_host_wm_client_request")?.max(1);
    let request_id = next_request_id();
    let request = format!(
        "request_id={request_id}\nclient_id={client_id}\nmethod={method}\nwindow_id={window_id}\ntitle_hex={}\nx={x}\ny={y}\nw={w}\nh={h}\ncontent_hex={}\nprocess_id={process_id}\napp_id_hex={}\n",
        hex_encode(&title),
        hex_encode(&content),
        hex_encode(&app_id)
    );
    write_atomic(&request_path(&dir, request_id), &request)
        .map_err(|e| CompileError::runtime(&format!("rt_host_wm_client_request write: {e}")))?;

    let reply = reply_path(&dir, request_id);
    let deadline = std::time::Instant::now() + Duration::from_millis(timeout_ms as u64);
    while std::time::Instant::now() < deadline {
        if let Ok(raw) = fs::read_to_string(&reply) {
            let _ = fs::remove_file(&reply);
            let kv = parse_kv(&raw);
            return Ok(Value::Tuple(vec![
                Value::Int(read_i64(&kv, "status")),
                Value::Int(read_i64(&kv, "window_id")),
            ]));
        }
        std::thread::sleep(Duration::from_millis(4));
    }
    Ok(Value::Tuple(vec![Value::Int(1), Value::Int(0)]))
}

pub fn rt_host_wm_client_poll_event(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Err(CompileError::runtime(
            "rt_host_wm_client_poll_event requires client_id and blocking",
        ));
    }
    let dir = match bridge_dir_from_env() {
        Some(dir) => dir,
        None => {
            return Ok(Value::Tuple(vec![
                Value::Int(0),
                Value::Int(0),
                Value::Int(0),
                Value::Int(0),
                Value::Int(0),
                Value::Int(0),
            ]))
        }
    };
    let client_id = get_i64(args, 0, "rt_host_wm_client_poll_event")?;
    let blocking = matches!(args.get(1), Some(Value::Bool(true)));
    let deadline = if blocking {
        Some(std::time::Instant::now() + Duration::from_secs(86_400))
    } else {
        Some(std::time::Instant::now())
    };
    loop {
        let mut paths: Vec<PathBuf> = fs::read_dir(dir.join("events"))
            .ok()
            .into_iter()
            .flat_map(|entries| entries.filter_map(|e| e.ok().map(|e| e.path())))
            .filter(|p| {
                p.file_name()
                    .and_then(|s| s.to_str())
                    .map(|name| name.starts_with(&format!("{client_id}_")) && name.ends_with(".evt"))
                    .unwrap_or(false)
            })
            .collect();
        paths.sort();
        if let Some(path) = paths.first() {
            if let Ok(raw) = fs::read_to_string(path) {
                let _ = fs::remove_file(path);
                let kv = parse_kv(&raw);
                return Ok(Value::Tuple(vec![
                    Value::Int(read_i64(&kv, "window_id")),
                    Value::Int(read_i64(&kv, "event_type")),
                    Value::Int(read_i64(&kv, "key")),
                    Value::Int(read_i64(&kv, "x")),
                    Value::Int(read_i64(&kv, "y")),
                    Value::Int(read_i64(&kv, "mods")),
                ]));
            }
        }
        if !blocking || deadline.map(|d| std::time::Instant::now() >= d).unwrap_or(false) {
            return Ok(Value::Tuple(vec![
                Value::Int(0),
                Value::Int(0),
                Value::Int(0),
                Value::Int(0),
                Value::Int(0),
                Value::Int(0),
            ]));
        }
        std::thread::sleep(Duration::from_millis(8));
    }
}
