//! Regex SFFI functions for the interpreter

use crate::error::CompileError;
use crate::value::Value;
use std::sync::{OnceLock, RwLock};

struct RegexSlot {
    generation: u32,
    value: Option<regex::Regex>,
}

#[derive(Default)]
struct RegexStore {
    slots: Vec<RegexSlot>,
    free: Vec<usize>,
}

static REGEX_STORE: OnceLock<RwLock<RegexStore>> = OnceLock::new();

fn regex_store() -> &'static RwLock<RegexStore> {
    REGEX_STORE.get_or_init(|| RwLock::new(RegexStore::default()))
}

fn runtime_error(message: impl Into<String>) -> CompileError {
    CompileError::Runtime(message.into())
}

fn expect_int(args: &[Value], index: usize, name: &str) -> Result<i64, CompileError> {
    match args.get(index) {
        Some(Value::Int(value)) => Ok(*value),
        _ => Err(runtime_error(format!("{} argument {} must be i64", name, index + 1))),
    }
}

fn expect_text<'a>(args: &'a [Value], index: usize, name: &str) -> Result<&'a str, CompileError> {
    match args.get(index) {
        Some(Value::Str(value)) => Ok(value.as_ref().as_str()),
        _ => Err(runtime_error(format!("{} argument {} must be text", name, index + 1))),
    }
}

fn encode_handle(index: usize, generation: u32) -> Result<i64, CompileError> {
    let slot = u32::try_from(index)
        .map_err(|_| runtime_error("regex handle table exhausted"))?
        .checked_add(1)
        .ok_or_else(|| runtime_error("regex handle table exhausted"))?;
    Ok(((u64::from(generation) << 32) | u64::from(slot)) as i64)
}

fn decode_handle(handle: i64) -> Result<(usize, u32), CompileError> {
    if handle <= 0 {
        return Err(runtime_error("invalid regex handle"));
    }
    let bits = handle as u64;
    let generation = (bits >> 32) as u32;
    let slot = (bits & u64::from(u32::MAX)) as u32;
    if generation == 0 || slot == 0 {
        return Err(runtime_error("invalid regex handle"));
    }
    Ok(((slot - 1) as usize, generation))
}

fn with_regex<T>(handle: i64, operation: impl FnOnce(&regex::Regex) -> T) -> Result<T, CompileError> {
    let (index, generation) = decode_handle(handle)?;
    let store = regex_store()
        .read()
        .map_err(|_| runtime_error("regex handle store poisoned"))?;
    let slot = store
        .slots
        .get(index)
        .filter(|slot| slot.generation == generation)
        .and_then(|slot| slot.value.as_ref())
        .ok_or_else(|| runtime_error("stale or unknown regex handle"))?;
    Ok(operation(slot))
}

/// rt_regex_new(pattern) -> generation-checked opaque i64 handle, or 0 when
/// the pattern is invalid. Compilation is the only allocation on this path.
pub fn rt_regex_new(args: &[Value]) -> Result<Value, CompileError> {
    let pattern = expect_text(args, 0, "rt_regex_new")?;
    let compiled = match regex::Regex::new(pattern) {
        Ok(value) => value,
        Err(_) => return Ok(Value::Int(0)),
    };
    let mut store = regex_store()
        .write()
        .map_err(|_| runtime_error("regex handle store poisoned"))?;
    let index = if let Some(index) = store.free.pop() {
        index
    } else {
        store.slots.push(RegexSlot {
            generation: 1,
            value: None,
        });
        store.slots.len() - 1
    };
    let generation = store.slots[index].generation;
    store.slots[index].value = Some(compiled);
    Ok(Value::Int(encode_handle(index, generation)?))
}

pub fn rt_regex_destroy(args: &[Value]) -> Result<Value, CompileError> {
    let handle = expect_int(args, 0, "rt_regex_destroy")?;
    let (index, generation) = decode_handle(handle)?;
    let mut store = regex_store()
        .write()
        .map_err(|_| runtime_error("regex handle store poisoned"))?;
    let slot = store
        .slots
        .get_mut(index)
        .filter(|slot| slot.generation == generation && slot.value.is_some())
        .ok_or_else(|| runtime_error("stale or unknown regex handle"))?;
    slot.value = None;
    slot.generation = if slot.generation == 0x7fff_ffff {
        1
    } else {
        slot.generation + 1
    };
    store.free.push(index);
    Ok(Value::Nil)
}

pub fn rt_regex_is_match(args: &[Value]) -> Result<Value, CompileError> {
    let handle = expect_int(args, 0, "rt_regex_is_match")?;
    let text = expect_text(args, 1, "rt_regex_is_match")?;
    Ok(Value::Int(if with_regex(handle, |value| value.is_match(text))? {
        1
    } else {
        0
    }))
}

pub fn rt_regex_find(args: &[Value]) -> Result<Value, CompileError> {
    let handle = expect_int(args, 0, "rt_regex_find")?;
    let text = expect_text(args, 1, "rt_regex_find")?;
    let found = with_regex(handle, |value| value.find(text).map(|item| item.as_str().to_owned()))?;
    Ok(Value::text(found.unwrap_or_default()))
}

pub fn rt_regex_find_all(args: &[Value]) -> Result<Value, CompileError> {
    let handle = expect_int(args, 0, "rt_regex_find_all")?;
    let text = expect_text(args, 1, "rt_regex_find_all")?;
    let result = with_regex(handle, |value| {
        value
            .find_iter(text)
            .map(|item| item.as_str())
            .collect::<Vec<_>>()
            .join("\n")
    })?;
    Ok(Value::text(result))
}

pub fn rt_regex_captures(args: &[Value]) -> Result<Value, CompileError> {
    let handle = expect_int(args, 0, "rt_regex_captures")?;
    let text = expect_text(args, 1, "rt_regex_captures")?;
    let result = with_regex(handle, |value| {
        value
            .captures(text)
            .map(|captures| {
                captures
                    .iter()
                    .map(|item| item.map_or("", |matched| matched.as_str()))
                    .collect::<Vec<_>>()
                    .join("\n")
            })
            .unwrap_or_default()
    })?;
    Ok(Value::text(result))
}

pub fn rt_regex_captures_len(args: &[Value]) -> Result<Value, CompileError> {
    let handle = expect_int(args, 0, "rt_regex_captures_len")?;
    let text = expect_text(args, 1, "rt_regex_captures_len")?;
    let count = with_regex(handle, |value| {
        value.captures(text).map_or(0, |captures| captures.len())
    })?;
    Ok(Value::Int(count as i64))
}

fn replace_handle(args: &[Value], all: bool, name: &str) -> Result<Value, CompileError> {
    let handle = expect_int(args, 0, name)?;
    let text = expect_text(args, 1, name)?;
    let replacement = expect_text(args, 2, name)?;
    let result = with_regex(handle, |value| {
        if all {
            value.replace_all(text, replacement)
        } else {
            value.replace(text, replacement)
        }
        .into_owned()
    })?;
    Ok(Value::text(result))
}

pub fn rt_regex_replace(args: &[Value]) -> Result<Value, CompileError> {
    replace_handle(args, false, "rt_regex_replace")
}

pub fn rt_regex_replace_all(args: &[Value]) -> Result<Value, CompileError> {
    replace_handle(args, true, "rt_regex_replace_all")
}

pub fn rt_regex_split(args: &[Value]) -> Result<Value, CompileError> {
    let handle = expect_int(args, 0, "rt_regex_split")?;
    let text = expect_text(args, 1, "rt_regex_split")?;
    let result = with_regex(handle, |value| value.split(text).collect::<Vec<_>>().join("\n"))?;
    Ok(Value::text(result))
}

fn quick_regex<'a>(args: &'a [Value], name: &str) -> Result<(regex::Regex, &'a str), CompileError> {
    let pattern = expect_text(args, 0, name)?;
    let text = expect_text(args, 1, name)?;
    let compiled = regex::Regex::new(pattern)
        .map_err(|error| CompileError::semantic(format!("invalid regex pattern: {}", error)))?;
    Ok((compiled, text))
}

pub fn rt_regex_is_match_quick(args: &[Value]) -> Result<Value, CompileError> {
    let pattern = expect_text(args, 0, "rt_regex_is_match_quick")?;
    let text = expect_text(args, 1, "rt_regex_is_match_quick")?;
    let compiled = match regex::Regex::new(pattern) {
        Ok(value) => value,
        Err(_) => return Ok(Value::Int(-1)),
    };
    Ok(Value::Int(if compiled.is_match(text) { 1 } else { 0 }))
}

pub fn rt_regex_find_quick(args: &[Value]) -> Result<Value, CompileError> {
    let (compiled, text) = quick_regex(args, "rt_regex_find_quick")?;
    Ok(Value::text(
        compiled.find(text).map_or("", |item| item.as_str()).to_owned(),
    ))
}

fn replace_quick(args: &[Value], all: bool, name: &str) -> Result<Value, CompileError> {
    let (compiled, text) = quick_regex(args, name)?;
    let replacement = expect_text(args, 2, name)?;
    let result = if all {
        compiled.replace_all(text, replacement)
    } else {
        compiled.replace(text, replacement)
    };
    Ok(Value::text(result.into_owned()))
}

pub fn rt_regex_replace_quick(args: &[Value]) -> Result<Value, CompileError> {
    replace_quick(args, false, "rt_regex_replace_quick")
}

pub fn rt_regex_replace_all_quick(args: &[Value]) -> Result<Value, CompileError> {
    replace_quick(args, true, "rt_regex_replace_all_quick")
}

pub fn rt_regex_split_quick(args: &[Value]) -> Result<Value, CompileError> {
    let (compiled, text) = quick_regex(args, "rt_regex_split_quick")?;
    Ok(Value::text(compiled.split(text).collect::<Vec<_>>().join("\n")))
}

/// sffi_regex_is_match(pattern, text) -> bool
pub fn is_match(args: &[Value]) -> Result<Value, CompileError> {
    let pattern = args.first().map(|v| v.to_display_string()).unwrap_or_default();
    let text = args.get(1).map(|v| v.to_display_string()).unwrap_or_default();
    match regex::Regex::new(&pattern) {
        Ok(re) => Ok(Value::Bool(re.is_match(&text))),
        Err(e) => Err(CompileError::semantic(format!("invalid regex pattern: {}", e))),
    }
}

/// sffi_regex_find(pattern, text) -> [text, start, end] or []
pub fn find(args: &[Value]) -> Result<Value, CompileError> {
    let pattern = args.first().map(|v| v.to_display_string()).unwrap_or_default();
    let text = args.get(1).map(|v| v.to_display_string()).unwrap_or_default();
    match regex::Regex::new(&pattern) {
        Ok(re) => {
            if let Some(m) = re.find(&text) {
                Ok(Value::array(vec![
                    Value::text(m.as_str().to_string()),
                    Value::Int(m.start() as i64),
                    Value::Int(m.end() as i64),
                ]))
            } else {
                Ok(Value::array(vec![]))
            }
        }
        Err(e) => Err(CompileError::semantic(format!("invalid regex pattern: {}", e))),
    }
}

/// sffi_regex_find_all(pattern, text) -> [[text, start, end], ...]
pub fn find_all(args: &[Value]) -> Result<Value, CompileError> {
    let pattern = args.first().map(|v| v.to_display_string()).unwrap_or_default();
    let text = args.get(1).map(|v| v.to_display_string()).unwrap_or_default();
    match regex::Regex::new(&pattern) {
        Ok(re) => {
            let results: Vec<Value> = re
                .find_iter(&text)
                .map(|m| {
                    Value::array(vec![
                        Value::text(m.as_str().to_string()),
                        Value::Int(m.start() as i64),
                        Value::Int(m.end() as i64),
                    ])
                })
                .collect();
            Ok(Value::array(results))
        }
        Err(e) => Err(CompileError::semantic(format!("invalid regex pattern: {}", e))),
    }
}

/// sffi_regex_captures(pattern, text) -> [full_match, group1, ...] or []
pub fn captures(args: &[Value]) -> Result<Value, CompileError> {
    let pattern = args.first().map(|v| v.to_display_string()).unwrap_or_default();
    let text = args.get(1).map(|v| v.to_display_string()).unwrap_or_default();
    match regex::Regex::new(&pattern) {
        Ok(re) => {
            if let Some(caps) = re.captures(&text) {
                let results: Vec<Value> = caps
                    .iter()
                    .map(|m| match m {
                        Some(m) => Value::text(m.as_str().to_string()),
                        None => Value::Nil,
                    })
                    .collect();
                Ok(Value::array(results))
            } else {
                Ok(Value::array(vec![]))
            }
        }
        Err(e) => Err(CompileError::semantic(format!("invalid regex pattern: {}", e))),
    }
}

/// sffi_regex_replace(pattern, text, replacement) -> text
pub fn replace(args: &[Value]) -> Result<Value, CompileError> {
    let pattern = args.first().map(|v| v.to_display_string()).unwrap_or_default();
    let text = args.get(1).map(|v| v.to_display_string()).unwrap_or_default();
    let replacement = args.get(2).map(|v| v.to_display_string()).unwrap_or_default();
    match regex::Regex::new(&pattern) {
        Ok(re) => Ok(Value::text(re.replace(&text, replacement.as_str()).to_string())),
        Err(e) => Err(CompileError::semantic(format!("invalid regex pattern: {}", e))),
    }
}

/// sffi_regex_replace_all(pattern, text, replacement) -> text
pub fn replace_all(args: &[Value]) -> Result<Value, CompileError> {
    let pattern = args.first().map(|v| v.to_display_string()).unwrap_or_default();
    let text = args.get(1).map(|v| v.to_display_string()).unwrap_or_default();
    let replacement = args.get(2).map(|v| v.to_display_string()).unwrap_or_default();
    match regex::Regex::new(&pattern) {
        Ok(re) => Ok(Value::text(re.replace_all(&text, replacement.as_str()).to_string())),
        Err(e) => Err(CompileError::semantic(format!("invalid regex pattern: {}", e))),
    }
}

/// sffi_regex_split(pattern, text) -> [text]
pub fn split(args: &[Value]) -> Result<Value, CompileError> {
    let pattern = args.first().map(|v| v.to_display_string()).unwrap_or_default();
    let text = args.get(1).map(|v| v.to_display_string()).unwrap_or_default();
    match regex::Regex::new(&pattern) {
        Ok(re) => {
            let parts: Vec<Value> = re.split(&text).map(|s| Value::text(s.to_string())).collect();
            Ok(Value::array(parts))
        }
        Err(e) => Err(CompileError::semantic(format!("invalid regex pattern: {}", e))),
    }
}

/// sffi_regex_split_n(pattern, text, limit) -> [text]
pub fn split_n(args: &[Value]) -> Result<Value, CompileError> {
    let pattern = args.first().map(|v| v.to_display_string()).unwrap_or_default();
    let text = args.get(1).map(|v| v.to_display_string()).unwrap_or_default();
    let limit = args.get(2).and_then(|v| v.as_int().ok()).unwrap_or(0) as usize;
    match regex::Regex::new(&pattern) {
        Ok(re) => {
            let parts: Vec<Value> = re.splitn(&text, limit).map(|s| Value::text(s.to_string())).collect();
            Ok(Value::array(parts))
        }
        Err(e) => Err(CompileError::semantic(format!("invalid regex pattern: {}", e))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn legacy_handle_is_generation_checked_and_match_is_typed() {
        let handle = rt_regex_new(&[Value::text(r"\d+")])
            .expect("valid pattern")
            .as_int()
            .expect("integer handle");
        assert!(handle > 0);
        assert_eq!(
            rt_regex_is_match(&[Value::Int(handle), Value::text("item 42")]).expect("live handle"),
            Value::Int(1)
        );
        rt_regex_destroy(&[Value::Int(handle)]).expect("first destroy");
        assert!(rt_regex_is_match(&[Value::Int(handle), Value::text("item 42")]).is_err());
    }

    #[test]
    fn invalid_patterns_use_declared_integer_sentinels() {
        assert_eq!(
            rt_regex_new(&[Value::text("[invalid")]).expect("typed sentinel"),
            Value::Int(0)
        );
        assert_eq!(
            rt_regex_is_match_quick(&[Value::text("[invalid"), Value::text("text")]).expect("typed sentinel"),
            Value::Int(-1)
        );
    }
}
