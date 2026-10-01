//! Execute the shared C capture engine with Rust-owned text and builder values.
use simple_runtime::value::{rt_array_new, rt_string_data, rt_string_len, rt_string_new, RuntimeValue};
use simple_runtime::value::sffi::capture_text::spl_collection_capture_text_copy;
use std::ffi::CString;
use std::sync::Mutex;

extern "C" {
    fn spl_collection_capture_begin(target: i64) -> i64;
    fn spl_collection_capture_note_size(site: i64, target: i64, size: i64) -> i64;
    fn spl_collection_capture_note_lookup(site: i64, target: i64, found: i64) -> i64;
    fn spl_collection_capture_note_materialization(site: i64, target: i64) -> i64;
    fn spl_collection_capture_note_hash_probe(site: i64, target: i64, probes: i64, collisions: i64) -> i64;
    fn spl_collection_capture_finish() -> i64;
    fn spl_collection_capture_abort() -> i64;
}

static CAPTURE_LOCK: Mutex<()> = Mutex::new(());

struct ResetCapture;
impl Drop for ResetCapture {
    fn drop(&mut self) {
        unsafe { spl_collection_capture_abort() };
    }
}

fn text(value: &str) -> i64 {
    rt_string_new(value.as_ptr(), value.len() as u64).to_raw() as i64
}

fn output(raw: i64) -> Option<String> {
    let value = RuntimeValue::from_raw(raw as u64);
    if value.is_nil() {
        return None;
    }
    let len = rt_string_len(value);
    assert!(len >= 0, "finish must return a Rust-owned string or nil");
    let data = rt_string_data(value);
    assert!(!data.is_null(), "Rust registry must recognize the returned text");
    Some(String::from_utf8(unsafe { std::slice::from_raw_parts(data, len as usize) }.to_vec()).unwrap())
}

#[test]
fn disabled_notes_do_not_decode_invalid_values() {
    let _lock = CAPTURE_LOCK.lock().unwrap_or_else(|error| error.into_inner());
    let _reset = ResetCapture;
    unsafe {
        assert_eq!(spl_collection_capture_abort(), 1);
        assert_eq!(spl_collection_capture_note_size(0, 0, -1), 1);
        assert_eq!(spl_collection_capture_note_lookup(0, 0, 2), 1);
        assert_eq!(spl_collection_capture_note_materialization(0, 0), 1);
        assert_eq!(spl_collection_capture_note_hash_probe(0, 0, -1, -1), 1);
        assert_eq!(output(spl_collection_capture_finish()), None);
    }
}

#[test]
fn all_capture_endpoints_use_the_rust_owner_abi() {
    let _lock = CAPTURE_LOCK.lock().unwrap_or_else(|error| error.into_inner());
    let _reset = ResetCapture;
    let target = text("x86_64-v3");
    let site = text("ast://capture/owner-abi#1");
    let wrong = text("other-target");
    unsafe {
        assert_eq!(spl_collection_capture_begin(target), 1);
        assert_eq!(spl_collection_capture_begin(target), 0);
        assert_eq!(spl_collection_capture_note_size(site, target, 2), 1);
        // A filtered event must not poison the capture, even with an invalid site.
        assert_eq!(spl_collection_capture_note_lookup(0, wrong, 2), 1);
        assert_eq!(spl_collection_capture_note_lookup(site, target, 1), 1);
        assert_eq!(spl_collection_capture_note_lookup(site, target, 0), 1);
        assert_eq!(spl_collection_capture_note_materialization(site, wrong), 1);
        assert_eq!(spl_collection_capture_note_materialization(site, target), 1);
        assert_eq!(spl_collection_capture_note_materialization(site, target), 1);
        assert_eq!(spl_collection_capture_note_hash_probe(site, wrong, 10, 9), 1);
        assert_eq!(spl_collection_capture_note_hash_probe(site, target, 3, 1), 1);
        assert_eq!(spl_collection_capture_note_hash_probe(site, target, 1, 0), 1);
        assert_eq!(spl_collection_capture_note_size(site, target, 0), 1);
        let body = output(spl_collection_capture_finish()).unwrap();
        assert!(body.starts_with("collection;sample=0;site=ast://capture/owner-abi#1;target=x86_64-v3;"));
        assert!(body.contains("size_p95=2;lookup_p95=2;hits_p95=1;misses_p95=1"));
        for (sample, name, value) in [
            (1, "collection_size", 2),
            (2, "lookup_count", 2),
            (3, "distinct_key_count", 0),
            (4, "materialization_count", 2),
            (5, "hash_probe_count", 4),
            (6, "hash_collision_count", 1),
        ] {
            assert!(body.contains(&format!(
                "metric;sample={sample};site=ast://capture/owner-abi#1;target=x86_64-v3;name={name};value={value}"
            )));
        }
        assert_eq!(output(spl_collection_capture_finish()), None);
        assert_eq!(spl_collection_capture_begin(target), 1);
        assert_eq!(spl_collection_capture_abort(), 1);
        assert_eq!(spl_collection_capture_begin(target), 1);
        assert_eq!(output(spl_collection_capture_finish()), Some(String::new()));
    }
}

#[test]
fn invalid_events_and_counter_overflow_fail_the_whole_capture() {
    let _lock = CAPTURE_LOCK.lock().unwrap_or_else(|error| error.into_inner());
    let _reset = ResetCapture;
    let target = text("x86_64-v3");
    let site = text("ast://capture/validation");
    unsafe {
        assert_eq!(spl_collection_capture_begin(text("bad;target")), 0);
        assert_eq!(spl_collection_capture_begin(text("")), 0);
        assert_eq!(spl_collection_capture_begin(text(&"x".repeat(257))), 0);
        for (probes, collisions) in [(0, 0), (1, -1), (1, 2)] {
            assert_eq!(spl_collection_capture_begin(target), 1);
            assert_eq!(
                spl_collection_capture_note_hash_probe(site, target, probes, collisions),
                0
            );
            assert_eq!(output(spl_collection_capture_finish()), None);
        }
        assert_eq!(spl_collection_capture_begin(target), 1);
        assert_eq!(spl_collection_capture_note_lookup(site, target, 2), 0);
        assert_eq!(output(spl_collection_capture_finish()), None);
        assert_eq!(spl_collection_capture_begin(target), 1);
        assert_eq!(spl_collection_capture_note_size(site, target, -1), 0);
        assert_eq!(output(spl_collection_capture_finish()), None);
        for invalid in ["not-ast", "ast://bad;site", "ast://bad\nsite"] {
            assert_eq!(spl_collection_capture_begin(target), 1);
            assert_eq!(spl_collection_capture_note_materialization(text(invalid), target), 0);
            assert_eq!(output(spl_collection_capture_finish()), None);
        }
        assert_eq!(spl_collection_capture_begin(target), 1);
        assert_eq!(
            spl_collection_capture_note_hash_probe(site, target, i64::MAX, i64::MAX),
            1
        );
        assert_eq!(spl_collection_capture_note_hash_probe(site, target, 1, 1), 0);
        assert_eq!(output(spl_collection_capture_finish()), None);
    }
}

#[test]
fn finish_orders_sites_and_omits_unobserved_probe_metrics() {
    let _lock = CAPTURE_LOCK.lock().unwrap_or_else(|error| error.into_inner());
    let _reset = ResetCapture;
    let target = text("x86_64-v3");
    unsafe {
        assert_eq!(spl_collection_capture_begin(target), 1);
        assert_eq!(
            spl_collection_capture_note_size(text("ast://capture/z"), text(""), 3),
            1
        );
        assert_eq!(spl_collection_capture_note_size(text("ast://capture/a"), target, 1), 1);
        let body = output(spl_collection_capture_finish()).unwrap();
        assert!(body.starts_with("collection;sample=0;site=ast://capture/a;"));
        assert!(body.contains("\ncollection;sample=1;site=ast://capture/z;"));
        assert!(!body.contains("hash_probe_count"));
        assert!(!body.contains("hash_collision_count"));
        assert_eq!(body.lines().count(), 10); // two collection + eight metric records
    }
}

#[test]
fn capture_bounds_sites_to_the_sprof_sample_budget() {
    let _lock = CAPTURE_LOCK.lock().unwrap_or_else(|error| error.into_inner());
    let _reset = ResetCapture;
    let target = text("x86_64-v3");
    unsafe {
        assert_eq!(spl_collection_capture_begin(target), 1);
        // Each site can emit one collection record and six metrics (100000 limit).
        for index in 0..14_285 {
            assert_eq!(
                spl_collection_capture_note_size(text(&format!("ast://capture/bound/{index}")), target, 1),
                1
            );
        }
        assert_eq!(
            spl_collection_capture_note_size(text("ast://capture/bound/overflow"), target, 1),
            0
        );
        assert_eq!(output(spl_collection_capture_finish()), None);
        assert_eq!(spl_collection_capture_begin(target), 1);
        assert_eq!(output(spl_collection_capture_finish()), Some(String::new()));
    }
}

#[test]
fn bounded_text_adapter_preserves_prefix_and_trusted_raw_c_inputs() {
    let _lock = CAPTURE_LOCK.lock().unwrap_or_else(|error| error.into_inner());
    let _reset = ResetCapture;
    let target = CString::new("raw-target").unwrap();
    let site = CString::new("ast://capture/raw").unwrap();
    unsafe {
        assert_eq!(spl_collection_capture_begin(target.as_ptr() as i64), 1);
        assert_eq!(spl_collection_capture_note_size(site.as_ptr() as i64, text(""), 2), 1);
        assert!(output(spl_collection_capture_finish())
            .unwrap()
            .contains("site=ast://capture/raw;target=raw-target;"));
        assert_eq!(spl_collection_capture_begin(text("prefix\0ignored;target")), 1);
        assert_eq!(
            spl_collection_capture_note_size(text("ast://capture/prefix\0ignored;site"), text("prefix"), 3),
            1
        );
        let body = output(spl_collection_capture_finish()).unwrap();
        assert!(body.contains("site=ast://capture/prefix;target=prefix;"));
        assert!(!body.contains("ignored"));
        let array = rt_array_new(0);
        assert_eq!(spl_collection_capture_begin(array.to_raw() as i64), 0);
        assert_eq!(spl_collection_capture_begin(text("prefix")), 1);
        // A failed target decode is filtered; a matching target with bad site poisons.
        assert_eq!(spl_collection_capture_note_size(0, array.to_raw() as i64, -1), 1);
        assert_eq!(
            spl_collection_capture_note_size(array.to_raw() as i64, text("prefix"), 1),
            0
        );
        assert_eq!(output(spl_collection_capture_finish()), None);
        let mut buffer = [0u8; 4097];
        assert_eq!(spl_collection_capture_text_copy(text("x"), std::ptr::null_mut(), 1), 0);
        assert_eq!(
            spl_collection_capture_text_copy(text("x"), buffer.as_mut_ptr(), 4097),
            0
        );
        assert_eq!(
            spl_collection_capture_text_copy(array.to_raw() as i64, buffer.as_mut_ptr(), 4096),
            0
        );
        assert_eq!(
            spl_collection_capture_text_copy((array.to_raw() & !7) as i64, buffer.as_mut_ptr(), 4096),
            0
        );
    }
}

#[test]
fn text_limits_are_measured_within_the_runtime_owned_bytes() {
    let _lock = CAPTURE_LOCK.lock().unwrap_or_else(|error| error.into_inner());
    let _reset = ResetCapture;
    let target = text(&"t".repeat(256));
    let site = text(&format!("ast://{}", "s".repeat(4090)));
    unsafe {
        assert_eq!(spl_collection_capture_begin(target), 1);
        assert_eq!(spl_collection_capture_note_size(site, target, 1), 1);
        assert!(output(spl_collection_capture_finish()).unwrap().contains("size_p95=1;"));
        assert_eq!(spl_collection_capture_begin(text(&"t".repeat(257))), 0);
        assert_eq!(spl_collection_capture_begin(target), 1);
        // Overlong targets are ignored, without decoding the invalid site.
        assert_eq!(spl_collection_capture_note_size(0, text(&"t".repeat(257)), -1), 1);
        assert_eq!(
            spl_collection_capture_note_size(text(&format!("ast://{}", "s".repeat(4091))), target, 1),
            0
        );
        assert_eq!(output(spl_collection_capture_finish()), None);
    }
}
