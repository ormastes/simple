use crate::error::CompileError;
use crate::value::Value;
use ring::{digest, hmac};

const SHA256_LEN: usize = 32;

fn expect_byte_array(name: &str, value: &Value) -> Result<Vec<u8>, CompileError> {
    match value {
        Value::Array(items) => items
            .iter()
            .map(|item| match item {
                Value::Int(byte) if (0..=255).contains(byte) => Ok(*byte as u8),
                Value::UInt { value, .. } if *value <= 255 => Ok(*value as u8),
                Value::Int(_) | Value::UInt { .. } => {
                    Err(CompileError::runtime(format!("{name} expects byte values in 0..255")))
                }
                _ => Err(CompileError::runtime(format!("{name} expects an array of integers"))),
            })
            .collect(),
        _ => Err(CompileError::runtime(format!("{name} expects an array argument"))),
    }
}

fn expect_length(name: &str, value: &Value) -> Result<usize, CompileError> {
    match value {
        Value::Int(n) if *n >= 0 => Ok(*n as usize),
        Value::UInt { value, .. } => Ok(*value as usize),
        _ => Err(CompileError::runtime(format!(
            "{name} expects a non-negative integer length"
        ))),
    }
}

fn bytes_value(bytes: &[u8]) -> Value {
    Value::array(bytes.iter().map(|byte| Value::Int(*byte as i64)).collect())
}

fn sha256_bytes(data: &[u8]) -> Vec<u8> {
    digest::digest(&digest::SHA256, data).as_ref().to_vec()
}

fn hmac_sha256(key: &[u8], data_parts: &[&[u8]]) -> Vec<u8> {
    let key = hmac::Key::new(hmac::HMAC_SHA256, key);
    let mut ctx = hmac::Context::with_key(&key);
    for part in data_parts {
        ctx.update(part);
    }
    ctx.sign().as_ref().to_vec()
}

fn hkdf_extract_sha256(salt: &[u8], ikm: &[u8]) -> Vec<u8> {
    hmac_sha256(salt, &[ikm])
}

fn hkdf_expand_sha256(prk: &[u8], info: &[u8], length: usize) -> Vec<u8> {
    let mut okm = Vec::with_capacity(length);
    let mut prev: Vec<u8> = Vec::new();
    let mut counter: u8 = 1;

    while okm.len() < length {
        let counter_buf = [counter];
        prev = hmac_sha256(prk, &[&prev, info, &counter_buf]);
        okm.extend_from_slice(&prev);
        counter = counter.wrapping_add(1);
    }

    okm.truncate(length);
    okm
}

fn tls13_hkdf_label(label_tail: &[u8], context: &[u8], length: usize) -> Vec<u8> {
    let mut label = Vec::with_capacity(6 + label_tail.len());
    label.extend_from_slice(b"tls13 ");
    label.extend_from_slice(label_tail);

    let mut info = Vec::with_capacity(2 + 1 + label.len() + 1 + context.len());
    info.push(((length >> 8) & 0xFF) as u8);
    info.push((length & 0xFF) as u8);
    info.push(label.len() as u8);
    info.extend_from_slice(&label);
    info.push(context.len() as u8);
    info.extend_from_slice(context);
    info
}

fn hkdf_expand_label_sha256(secret: &[u8], label_tail: &[u8], context: &[u8], length: usize) -> Vec<u8> {
    let info = tls13_hkdf_label(label_tail, context, length);
    hkdf_expand_sha256(secret, &info, length)
}

fn expand_label_fixed(
    args: &[Value],
    label_tail: &[u8],
    context_arg: Option<&Value>,
    length: usize,
    name: &str,
) -> Result<Value, CompileError> {
    let secret = expect_byte_array(name, &args[0])?;
    let context = if let Some(value) = context_arg {
        expect_byte_array(name, value)?
    } else {
        Vec::new()
    };
    Ok(bytes_value(&hkdf_expand_label_sha256(
        &secret, label_tail, &context, length,
    )))
}

pub fn rt_tls13_sha256(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("rt_tls13_sha256 expects 1 argument".to_string()));
    }
    let data = expect_byte_array("rt_tls13_sha256", &args[0])?;
    Ok(bytes_value(&sha256_bytes(&data)))
}

pub fn rt_tls13_hkdf_extract(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::runtime(
            "rt_tls13_hkdf_extract expects 2 arguments".to_string(),
        ));
    }
    let salt = expect_byte_array("rt_tls13_hkdf_extract", &args[0])?;
    let ikm = expect_byte_array("rt_tls13_hkdf_extract", &args[1])?;
    Ok(bytes_value(&hkdf_extract_sha256(&salt, &ikm)))
}

pub fn rt_tls13_hkdf_extract_into(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 3 {
        return Err(CompileError::runtime(
            "rt_tls13_hkdf_extract_into expects 3 arguments".to_string(),
        ));
    }
    let _salt = expect_byte_array("rt_tls13_hkdf_extract_into", &args[0])?;
    let _ikm = expect_byte_array("rt_tls13_hkdf_extract_into", &args[1])?;
    let _out = expect_byte_array("rt_tls13_hkdf_extract_into", &args[2])?;
    Ok(Value::Int(0))
}

pub fn rt_tls13_hkdf_expand_into(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 4 {
        return Err(CompileError::runtime(
            "rt_tls13_hkdf_expand_into expects 4 arguments".to_string(),
        ));
    }
    let _prk = expect_byte_array("rt_tls13_hkdf_expand_into", &args[0])?;
    let _info = expect_byte_array("rt_tls13_hkdf_expand_into", &args[1])?;
    let _out = expect_byte_array("rt_tls13_hkdf_expand_into", &args[2])?;
    let _len = expect_length("rt_tls13_hkdf_expand_into", &args[3])?;
    Ok(Value::Int(0))
}

pub fn rt_tls13_hkdf_expand_label(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 4 {
        return Err(CompileError::runtime(
            "rt_tls13_hkdf_expand_label expects 4 arguments".to_string(),
        ));
    }
    let secret = expect_byte_array("rt_tls13_hkdf_expand_label", &args[0])?;
    let label_tail = expect_byte_array("rt_tls13_hkdf_expand_label", &args[1])?;
    let context = expect_byte_array("rt_tls13_hkdf_expand_label", &args[2])?;
    let length = expect_length("rt_tls13_hkdf_expand_label", &args[3])?;
    Ok(bytes_value(&hkdf_expand_label_sha256(
        &secret,
        &label_tail,
        &context,
        length,
    )))
}

pub fn rt_tls13_hkdf_expand_label_into(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 5 {
        return Err(CompileError::runtime(
            "rt_tls13_hkdf_expand_label_into expects 5 arguments".to_string(),
        ));
    }
    let _secret = expect_byte_array("rt_tls13_hkdf_expand_label_into", &args[0])?;
    let _label_tail = expect_byte_array("rt_tls13_hkdf_expand_label_into", &args[1])?;
    let _context = expect_byte_array("rt_tls13_hkdf_expand_label_into", &args[2])?;
    let _out = expect_byte_array("rt_tls13_hkdf_expand_label_into", &args[3])?;
    let _len = expect_length("rt_tls13_hkdf_expand_label_into", &args[4])?;
    Ok(Value::Int(0))
}

pub fn rt_tls13_hkdf_expand_label_derived(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::runtime(
            "rt_tls13_hkdf_expand_label_derived expects 2 arguments".to_string(),
        ));
    }
    expand_label_fixed(
        args,
        b"derived",
        Some(&args[1]),
        SHA256_LEN,
        "rt_tls13_hkdf_expand_label_derived",
    )
}

pub fn rt_tls13_hkdf_expand_label_key(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime(
            "rt_tls13_hkdf_expand_label_key expects 1 argument".to_string(),
        ));
    }
    expand_label_fixed(args, b"key", None, 16, "rt_tls13_hkdf_expand_label_key")
}

pub fn rt_tls13_hkdf_expand_label_iv(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime(
            "rt_tls13_hkdf_expand_label_iv expects 1 argument".to_string(),
        ));
    }
    expand_label_fixed(args, b"iv", None, 12, "rt_tls13_hkdf_expand_label_iv")
}

pub fn rt_tls13_hkdf_expand_label_finished(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime(
            "rt_tls13_hkdf_expand_label_finished expects 1 argument".to_string(),
        ));
    }
    expand_label_fixed(
        args,
        b"finished",
        None,
        SHA256_LEN,
        "rt_tls13_hkdf_expand_label_finished",
    )
}

pub fn rt_tls13_hkdf_expand_label_client_hs(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::runtime(
            "rt_tls13_hkdf_expand_label_client_hs expects 2 arguments".to_string(),
        ));
    }
    expand_label_fixed(
        args,
        b"c hs traffic",
        Some(&args[1]),
        SHA256_LEN,
        "rt_tls13_hkdf_expand_label_client_hs",
    )
}

pub fn rt_tls13_hkdf_expand_label_server_hs(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::runtime(
            "rt_tls13_hkdf_expand_label_server_hs expects 2 arguments".to_string(),
        ));
    }
    expand_label_fixed(
        args,
        b"s hs traffic",
        Some(&args[1]),
        SHA256_LEN,
        "rt_tls13_hkdf_expand_label_server_hs",
    )
}

pub fn rt_tls13_hkdf_expand_label_client_app(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::runtime(
            "rt_tls13_hkdf_expand_label_client_app expects 2 arguments".to_string(),
        ));
    }
    expand_label_fixed(
        args,
        b"c ap traffic",
        Some(&args[1]),
        SHA256_LEN,
        "rt_tls13_hkdf_expand_label_client_app",
    )
}

pub fn rt_tls13_hkdf_expand_label_server_app(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::runtime(
            "rt_tls13_hkdf_expand_label_server_app expects 2 arguments".to_string(),
        ));
    }
    expand_label_fixed(
        args,
        b"s ap traffic",
        Some(&args[1]),
        SHA256_LEN,
        "rt_tls13_hkdf_expand_label_server_app",
    )
}
