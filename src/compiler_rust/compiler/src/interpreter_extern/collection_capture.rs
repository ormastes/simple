//! Interpreter adapters for the stable `spl_` collection ABI: the erased
//! ordered-key comparator and the process-scoped collection capture channel.
//!
//! The Rust runtime (`ordered_key.rs`) and the shared C capture engine
//! (`runtime_collection_capture.c`) are the single owners; these entries only
//! marshal interpreter values into the runtime's word representation, so the
//! seed interpreter and native code agree on key order and capture events.

use super::common::{get_int, get_string, require_args};
use crate::error::CompileError;
use crate::runtime_bridge::{runtime_to_value, value_to_runtime};
use crate::value::Value;
use simple_runtime::value::sffi::ordered_key::spl_ordered_key_cmp as runtime_ordered_key_cmp;

extern "C" {
    fn spl_collection_capture_begin(target: i64) -> i64;
    fn spl_collection_capture_note_size(site: i64, target: i64, size: i64) -> i64;
    fn spl_collection_capture_note_lookup(site: i64, target: i64, found: i64) -> i64;
    fn spl_collection_capture_note_materialization(site: i64, target: i64) -> i64;
    fn spl_collection_capture_note_hash_probe(site: i64, target: i64, probes: i64, collisions: i64) -> i64;
    fn spl_collection_capture_note_filter(site: i64, target: i64, evaluated: i64, accepted: i64) -> i64;
    fn spl_collection_capture_note_loop(site: i64, target: i64, trips: i64) -> i64;
    fn spl_collection_capture_finish() -> i64;
    fn spl_collection_capture_abort() -> i64;
}

fn word(value: &Value) -> i64 {
    value_to_runtime(value).to_raw() as i64
}

fn text_word(args: &[Value], index: usize, name: &str) -> Result<i64, CompileError> {
    get_string(args, index, name)?;
    Ok(word(&args[index]))
}

fn site_target(args: &[Value], name: &str) -> Result<(i64, i64), CompileError> {
    Ok((text_word(args, 0, name)?, text_word(args, 1, name)?))
}

pub fn spl_ordered_key_cmp(args: &[Value]) -> Result<Value, CompileError> {
    require_args(args, 2, "spl_ordered_key_cmp")?;
    Ok(Value::Int(runtime_ordered_key_cmp(word(&args[0]), word(&args[1]))))
}

pub fn capture_begin(args: &[Value]) -> Result<Value, CompileError> {
    const NAME: &str = "spl_collection_capture_begin";
    require_args(args, 1, NAME)?;
    let target = text_word(args, 0, NAME)?;
    Ok(Value::Int(unsafe { spl_collection_capture_begin(target) }))
}

pub fn capture_note_size(args: &[Value]) -> Result<Value, CompileError> {
    const NAME: &str = "spl_collection_capture_note_size";
    require_args(args, 3, NAME)?;
    let (site, target) = site_target(args, NAME)?;
    let size = get_int(args, 2, NAME)?;
    Ok(Value::Int(unsafe { spl_collection_capture_note_size(site, target, size) }))
}

pub fn capture_note_lookup(args: &[Value]) -> Result<Value, CompileError> {
    const NAME: &str = "spl_collection_capture_note_lookup";
    require_args(args, 3, NAME)?;
    let (site, target) = site_target(args, NAME)?;
    let found = get_int(args, 2, NAME)?;
    Ok(Value::Int(unsafe { spl_collection_capture_note_lookup(site, target, found) }))
}

pub fn capture_note_materialization(args: &[Value]) -> Result<Value, CompileError> {
    const NAME: &str = "spl_collection_capture_note_materialization";
    require_args(args, 2, NAME)?;
    let (site, target) = site_target(args, NAME)?;
    Ok(Value::Int(unsafe { spl_collection_capture_note_materialization(site, target) }))
}

pub fn capture_note_hash_probe(args: &[Value]) -> Result<Value, CompileError> {
    const NAME: &str = "spl_collection_capture_note_hash_probe";
    require_args(args, 4, NAME)?;
    let (site, target) = site_target(args, NAME)?;
    let (probes, collisions) = (get_int(args, 2, NAME)?, get_int(args, 3, NAME)?);
    Ok(Value::Int(unsafe { spl_collection_capture_note_hash_probe(site, target, probes, collisions) }))
}

pub fn capture_note_filter(args: &[Value]) -> Result<Value, CompileError> {
    const NAME: &str = "spl_collection_capture_note_filter";
    require_args(args, 4, NAME)?;
    let (site, target) = site_target(args, NAME)?;
    let (evaluated, accepted) = (get_int(args, 2, NAME)?, get_int(args, 3, NAME)?);
    Ok(Value::Int(unsafe { spl_collection_capture_note_filter(site, target, evaluated, accepted) }))
}

pub fn capture_note_loop(args: &[Value]) -> Result<Value, CompileError> {
    const NAME: &str = "spl_collection_capture_note_loop";
    require_args(args, 3, NAME)?;
    let (site, target) = site_target(args, NAME)?;
    let trips = get_int(args, 2, NAME)?;
    Ok(Value::Int(unsafe { spl_collection_capture_note_loop(site, target, trips) }))
}

pub fn capture_finish(_args: &[Value]) -> Result<Value, CompileError> {
    let raw = unsafe { spl_collection_capture_finish() };
    Ok(runtime_to_value(simple_runtime::value::RuntimeValue::from_raw(raw as u64)))
}

pub fn capture_abort(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(unsafe { spl_collection_capture_abort() }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Mutex;

    static CAPTURE_LOCK: Mutex<()> = Mutex::new(());

    struct ResetCapture;
    impl Drop for ResetCapture {
        fn drop(&mut self) {
            let _ = capture_abort(&[]);
        }
    }

    fn s(v: &str) -> Value {
        Value::text(v)
    }

    #[test]
    fn ordered_key_cmp_orders_ints_and_text() {
        let cmp = |a: Value, b: Value| spl_ordered_key_cmp(&[a, b]).unwrap();
        assert_eq!(cmp(Value::Int(1), Value::Int(2)), Value::Int(-1));
        assert_eq!(cmp(Value::Int(7), Value::Int(7)), Value::Int(0));
        assert_eq!(cmp(Value::Int(9), Value::Int(-3)), Value::Int(1));
        assert_eq!(cmp(s("apple"), s("banana")), Value::Int(-1));
        assert_eq!(cmp(s("pear"), s("pear")), Value::Int(0));
        assert_eq!(cmp(s("b"), s("a")), Value::Int(1));
    }

    #[test]
    fn ordered_key_cmp_rejects_mixed_text_and_int() {
        assert_eq!(spl_ordered_key_cmp(&[s("a"), Value::Int(1)]).unwrap(), Value::Int(2));
    }

    #[test]
    fn capture_disabled_notes_are_accepted_and_finish_is_nil() {
        let _lock = CAPTURE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let _reset = ResetCapture;
        assert_eq!(capture_abort(&[]).unwrap(), Value::Int(1));
        let args = [s("site"), s("tgt"), Value::Int(3)];
        assert_eq!(capture_note_size(&args).unwrap(), Value::Int(1));
        assert_eq!(capture_finish(&[]).unwrap(), Value::Nil);
    }

    #[test]
    fn capture_begin_note_finish_round_trip() {
        let _lock = CAPTURE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let _reset = ResetCapture;
        assert_eq!(capture_begin(&[s("x86_64-v3")]).unwrap(), Value::Int(1));
        let sz = [s("a.spl:1"), s("x86_64-v3"), Value::Int(5)];
        assert_eq!(capture_note_size(&sz).unwrap(), Value::Int(1));
        let lk = [s("a.spl:2"), s("x86_64-v3"), Value::Int(1)];
        assert_eq!(capture_note_lookup(&lk).unwrap(), Value::Int(1));
        let lp = [s("a.spl:3"), s("x86_64-v3"), Value::Int(4)];
        assert_eq!(capture_note_loop(&lp).unwrap(), Value::Int(1));
        match capture_finish(&[]).unwrap() {
            Value::Str(text) => assert!(text.contains("a.spl:1"), "missing site in {text}"),
            other => panic!("finish must return text, got {other:?}"),
        }
    }

    #[test]
    fn capture_entries_reject_non_text_site() {
        assert!(capture_note_size(&[Value::Int(1), s("t"), Value::Int(1)]).is_err());
    }
}
