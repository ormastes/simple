// Packed word storage for `Value::Array` (ArrayData): every observable result
// must equal the boxed `Vec<Value>` it replaces.
// doc/05_design/compiler/interpreter/packed_word_array_storage_2026-10-05.md

fn pw_u32(v: u64) -> Value {
    Value::UInt { value: v, width: 32 }
}

/// A packed and a boxed array with the same elements.
fn pw_pair(value: Value, n: usize) -> (ArrayData, ArrayData) {
    let packed = ArrayData::repeat(value.clone(), n);
    let boxed = ArrayData::from(vec![value; n]);
    (packed, boxed)
}

fn pw_assert_same(packed: &ArrayData, boxed: &ArrayData) {
    assert_eq!(packed.len(), boxed.len());
    for i in 0..boxed.len() {
        assert_eq!(packed.get_value(i), boxed.get_value(i), "element {i}");
    }
    assert!(packed == boxed && boxed == packed);
    assert_eq!(format!("{packed:?}"), format!("{boxed:?}"));
    assert_eq!(packed.to_vec(), boxed.to_vec());
}

#[test]
fn packed_repeat_is_packed_only_for_large_in_domain_values() {
    assert!(ArrayData::repeat(Value::Int(0), PACKED_WORDS_MIN_LEN).is_packed());
    assert!(ArrayData::repeat(pw_u32(7), PACKED_WORDS_MIN_LEN).is_packed());
    assert!(!ArrayData::repeat(Value::Int(0), PACKED_WORDS_MIN_LEN - 1).is_packed());
    assert!(!ArrayData::repeat(Value::Int(-1), PACKED_WORDS_MIN_LEN).is_packed());
    assert!(!ArrayData::repeat(Value::Int(i64::from(u32::MAX) + 1), PACKED_WORDS_MIN_LEN).is_packed());
    assert!(!ArrayData::repeat(Value::UInt { value: 1, width: 8 }, PACKED_WORDS_MIN_LEN).is_packed());
    assert!(!ArrayData::repeat(Value::Float(0.0), PACKED_WORDS_MIN_LEN).is_packed());
}

#[test]
fn packed_reads_return_exactly_the_stored_value_kind() {
    let n = PACKED_WORDS_MIN_LEN;
    for v in [Value::Int(0), Value::Int(i64::from(u32::MAX)), pw_u32(0), pw_u32(u64::from(u32::MAX))] {
        let (packed, boxed) = pw_pair(v, n);
        assert!(packed.is_packed());
        pw_assert_same(&packed, &boxed);
    }
}

#[test]
fn packed_assign_index_matches_boxed_for_every_store_shape() {
    let n = PACKED_WORDS_MIN_LEN;
    // In-domain overwrites of either kind keep it packed.
    let (mut packed, mut boxed) = pw_pair(Value::Int(0), n);
    for (i, v) in [(0, pw_u32(0xFFFF_FFFF)), (5, Value::Int(3)), (n - 1, pw_u32(9)), (5, pw_u32(3))] {
        packed.assign_index(i, v.clone());
        boxed.assign_index(i, v);
    }
    assert!(packed.is_packed());
    pw_assert_same(&packed, &boxed);
    // A store outside the domain (mid-"loop") converts to boxed, same elements.
    for v in [Value::Int(-1), Value::Float(1.5), Value::Nil, Value::UInt { value: 1, width: 8 }] {
        let (mut packed, mut boxed) = pw_pair(pw_u32(1), n);
        packed.assign_index(7, v.clone());
        boxed.assign_index(7, v);
        assert!(!packed.is_packed());
        pw_assert_same(&packed, &boxed);
    }
    // Growth (index at and past the end) pads with nil exactly like boxed.
    let (mut packed, mut boxed) = pw_pair(Value::Int(1), n);
    packed.assign_index(n + 2, Value::Int(5));
    boxed.assign_index(n + 2, Value::Int(5));
    pw_assert_same(&packed, &boxed);
    assert_eq!(packed.get_value(n), Some(Value::Nil));
}

#[test]
fn packed_write_span_matches_boxed_including_self_overlap() {
    let n = PACKED_WORDS_MIN_LEN;
    let mut src_vals: Vec<Value> = (0..n).map(|i| if i % 3 == 0 { Value::Int(i as i64) } else { pw_u32(i as u64) }).collect();
    let src_boxed = ArrayData::from(src_vals.clone());
    // packed destination, boxed in-domain source -> stays packed
    let (mut packed, mut boxed) = pw_pair(Value::Int(0), n);
    packed.write_span_from(&src_boxed, 10, 3, 100);
    boxed.write_span_from(&src_boxed, 10, 3, 100);
    assert!(packed.is_packed());
    pw_assert_same(&packed, &boxed);
    // packed -> packed self-overlap from a snapshot (memmove semantics)
    let snapshot = packed.clone();
    let mut boxed_copy = boxed.clone();
    let boxed_snapshot = boxed.clone();
    packed.write_span_from(&snapshot, 12, 10, 50);
    boxed_copy.write_span_from(&boxed_snapshot, 12, 10, 50);
    pw_assert_same(&packed, &boxed_copy);
    // an out-of-domain source element converts the destination, same elements
    src_vals[4] = Value::Int(-9);
    let src_bad = ArrayData::from(src_vals);
    let (mut packed, mut boxed) = pw_pair(Value::Int(0), n);
    packed.write_span_from(&src_bad, 0, 0, 10);
    boxed.write_span_from(&src_bad, 0, 0, 10);
    assert!(!packed.is_packed());
    pw_assert_same(&packed, &boxed);
}

#[test]
fn deref_view_is_consistent_and_deref_mut_converts() {
    let n = PACKED_WORDS_MIN_LEN;
    let (mut packed, boxed) = pw_pair(pw_u32(4), n);
    let view: &Vec<Value> = &packed;
    assert_eq!(view, &*boxed);
    assert!(packed.is_packed(), "a read-only view does not convert");
    // A packed-aware write after a view drops the view; the next view is fresh.
    packed.assign_index(0, Value::Int(1));
    let view: &Vec<Value> = &packed;
    assert_eq!(view[0], Value::Int(1));
    // Any &mut Vec access converts to boxed permanently.
    let raw: &mut Vec<Value> = &mut packed;
    raw.push(Value::Int(2));
    assert!(!packed.is_packed());
    assert_eq!(packed.len(), n + 1);
    assert_eq!(packed.get_value(0), Some(Value::Int(1)));
}

#[test]
fn packed_clone_is_independent_copy_on_write() {
    let n = PACKED_WORDS_MIN_LEN;
    let shared = std::sync::Arc::new(ArrayData::repeat(Value::Int(0), n));
    let mut writer = std::sync::Arc::clone(&shared);
    std::sync::Arc::make_mut(&mut writer).assign_index(3, Value::Int(9));
    assert_eq!(shared.get_value(3), Some(Value::Int(0)), "the alias is unchanged");
    assert_eq!(writer.get_value(3), Some(Value::Int(9)));
    assert!(shared.is_packed() && writer.is_packed());
}

#[test]
fn value_equality_across_representations() {
    let n = PACKED_WORDS_MIN_LEN;
    let (packed, boxed) = pw_pair(Value::Int(2), n);
    let a = Value::Array(std::sync::Arc::new(packed));
    let b = Value::Array(std::sync::Arc::new(boxed));
    assert_eq!(a, b);
    let (packed, _) = pw_pair(Value::Int(2), n);
    let c = Value::Array(std::sync::Arc::new(packed));
    let d = Value::Array(std::sync::Arc::new(ArrayData::from(vec![pw_u32(2); n])));
    assert_eq!(c == d, Value::Int(2) == pw_u32(2), "element kind equality is the boxed rule");
}
