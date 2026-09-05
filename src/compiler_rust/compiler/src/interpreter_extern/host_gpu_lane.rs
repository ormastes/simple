//! Host/GPU lane marker runtime counters for interpreter extern calls.

use crate::error::CompileError;
use crate::value::Value;
use simple_runtime::host_gpu_lane;

pub fn rt_host_gpu_lane_event(args: &[Value]) -> Result<Value, CompileError> {
    let lane = match args.first() {
        Some(Value::Int(v)) => *v,
        _ => {
            return Err(CompileError::Runtime(
                "rt_host_gpu_lane_event expects lane code".to_string(),
            ))
        }
    };
    let phase = match args.get(1) {
        Some(Value::Int(v)) => *v,
        _ => {
            return Err(CompileError::Runtime(
                "rt_host_gpu_lane_event expects phase code".to_string(),
            ))
        }
    };
    Ok(Value::Int(host_gpu_lane::rt_host_gpu_lane_event(lane, phase)))
}

pub fn rt_host_gpu_lane_reset(_args: &[Value]) -> Result<Value, CompileError> {
    host_gpu_lane::rt_host_gpu_lane_reset();
    Ok(Value::Nil)
}

pub fn rt_host_gpu_lane_event_count(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(host_gpu_lane::rt_host_gpu_lane_event_count()))
}

pub fn rt_host_gpu_lane_begin_count(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(host_gpu_lane::rt_host_gpu_lane_begin_count()))
}

pub fn rt_host_gpu_lane_end_count(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(host_gpu_lane::rt_host_gpu_lane_end_count()))
}

pub fn rt_host_gpu_lane_last_lane(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(host_gpu_lane::rt_host_gpu_lane_last_lane()))
}

pub fn rt_host_gpu_lane_last_phase(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(host_gpu_lane::rt_host_gpu_lane_last_phase()))
}

pub fn rt_host_gpu_queue_reset(_args: &[Value]) -> Result<Value, CompileError> {
    host_gpu_lane::rt_host_gpu_queue_reset();
    Ok(Value::Nil)
}

pub fn rt_host_gpu_queue_emit(args: &[Value]) -> Result<Value, CompileError> {
    let lane = expect_int(args.first(), "rt_host_gpu_queue_emit expects lane code")?;
    let kind = expect_int(args.get(1), "rt_host_gpu_queue_emit expects kind code")?;
    let payload_size = expect_int(args.get(2), "rt_host_gpu_queue_emit expects payload size")?;
    let backend = expect_int(args.get(3), "rt_host_gpu_queue_emit expects backend code")?;
    Ok(Value::Int(host_gpu_lane::rt_host_gpu_queue_emit(
        lane,
        kind,
        payload_size,
        backend,
    )))
}

pub fn rt_host_gpu_queue_emit_payload(args: &[Value]) -> Result<Value, CompileError> {
    let lane = expect_int(args.first(), "rt_host_gpu_queue_emit_payload expects lane code")?;
    let kind = expect_int(args.get(1), "rt_host_gpu_queue_emit_payload expects kind code")?;
    let payload_size = expect_int(args.get(2), "rt_host_gpu_queue_emit_payload expects payload size")?;
    let backend = expect_int(args.get(3), "rt_host_gpu_queue_emit_payload expects backend code")?;
    let payload_hash = expect_int(args.get(4), "rt_host_gpu_queue_emit_payload expects payload hash")?;
    Ok(Value::Int(host_gpu_lane::rt_host_gpu_queue_emit_payload(
        lane,
        kind,
        payload_size,
        backend,
        payload_hash,
    )))
}

pub fn rt_host_gpu_queue_emit_payload_text(args: &[Value]) -> Result<Value, CompileError> {
    let lane = expect_int(args.first(), "rt_host_gpu_queue_emit_payload_text expects lane code")?;
    let kind = expect_int(args.get(1), "rt_host_gpu_queue_emit_payload_text expects kind code")?;
    let payload_size = expect_int(args.get(2), "rt_host_gpu_queue_emit_payload_text expects payload size")?;
    let backend = expect_int(args.get(3), "rt_host_gpu_queue_emit_payload_text expects backend code")?;
    let payload_hash = expect_int(args.get(4), "rt_host_gpu_queue_emit_payload_text expects payload hash")?;
    let payload_text = expect_text(args.get(5), "rt_host_gpu_queue_emit_payload_text expects payload text")?;
    Ok(Value::Int(host_gpu_lane::rt_host_gpu_queue_emit_payload_text(
        lane,
        kind,
        payload_size,
        backend,
        payload_hash,
        &payload_text,
    )))
}

pub fn rt_host_gpu_queue_drain(args: &[Value]) -> Result<Value, CompileError> {
    let max_packets = expect_int(args.first(), "rt_host_gpu_queue_drain expects max packet count")?;
    Ok(Value::Int(host_gpu_lane::rt_host_gpu_queue_drain(max_packets)))
}

pub fn rt_host_gpu_queue_submit(args: &[Value]) -> Result<Value, CompileError> {
    let max_packets = expect_int(args.first(), "rt_host_gpu_queue_submit expects max packet count")?;
    Ok(Value::Int(host_gpu_lane::rt_host_gpu_queue_submit(max_packets)))
}

pub fn rt_host_gpu_queue_complete(args: &[Value]) -> Result<Value, CompileError> {
    let max_packets = expect_int(args.first(), "rt_host_gpu_queue_complete expects max packet count")?;
    Ok(Value::Int(host_gpu_lane::rt_host_gpu_queue_complete(max_packets)))
}

pub fn rt_host_gpu_queue_packet_count(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(host_gpu_lane::rt_host_gpu_queue_packet_count()))
}

pub fn rt_host_gpu_queue_submitted_count(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(host_gpu_lane::rt_host_gpu_queue_submitted_count()))
}

pub fn rt_host_gpu_queue_completed_count(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(host_gpu_lane::rt_host_gpu_queue_completed_count()))
}

pub fn rt_host_gpu_queue_in_flight_count(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(host_gpu_lane::rt_host_gpu_queue_in_flight_count()))
}

pub fn rt_host_gpu_queue_last_status(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(host_gpu_lane::rt_host_gpu_queue_last_status()))
}

pub fn rt_host_gpu_queue_last_backend_handle(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(host_gpu_lane::rt_host_gpu_queue_last_backend_handle()))
}

pub fn rt_host_gpu_queue_last_device_time_us(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(host_gpu_lane::rt_host_gpu_queue_last_device_time_us()))
}

pub fn rt_host_gpu_queue_last_payload_size(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(host_gpu_lane::rt_host_gpu_queue_last_payload_size()))
}

pub fn rt_host_gpu_queue_last_payload_hash(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(host_gpu_lane::rt_host_gpu_queue_last_payload_hash()))
}

pub fn rt_host_gpu_queue_last_payload_text(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::text(host_gpu_lane::rt_host_gpu_queue_last_payload_text()))
}

fn expect_int(value: Option<&Value>, message: &str) -> Result<i64, CompileError> {
    match value {
        Some(Value::Int(v)) => Ok(*v),
        _ => Err(CompileError::Runtime(message.to_string())),
    }
}

fn expect_text(value: Option<&Value>, message: &str) -> Result<String, CompileError> {
    match value {
        Some(Value::Str(s)) => Ok(s.as_ref().clone()),
        _ => Err(CompileError::Runtime(message.to_string())),
    }
}
