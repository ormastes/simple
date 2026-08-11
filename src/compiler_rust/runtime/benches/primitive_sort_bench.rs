use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use simple_runtime::value::primitive_sort::{sort_runtime_values, sort_runtime_values_auto};
use simple_runtime::value::RuntimeValue;
use simple_simd::{detect_profile, SimdTier};

fn build_int_values(len: usize) -> Vec<RuntimeValue> {
    (0..len)
        .rev()
        .map(|index| RuntimeValue::from_int((index % 65_537) as i64 - 32_768))
        .collect()
}

fn build_float_values(len: usize) -> Vec<RuntimeValue> {
    (0..len)
        .rev()
        .map(|index| RuntimeValue::from_float(((index % 8_191) as f64 * 0.25) - 1_024.0))
        .collect()
}

fn build_byte_values(len: usize) -> Vec<RuntimeValue> {
    (0..len)
        .rev()
        .map(|index| RuntimeValue::from_int(((index * 29) % 251) as i64))
        .collect()
}

fn tagged_int_sort(values: &mut [RuntimeValue]) {
    values.sort_by_key(|left| left.as_int());
}

fn tagged_float_sort(values: &mut [RuntimeValue]) {
    values.sort_by(|left, right| left.as_float().total_cmp(&right.as_float()));
}

fn tagged_byte_sort(values: &mut [RuntimeValue]) {
    values.sort_by_key(|left| left.as_int());
}

fn bench_primitive_runtime_sort(c: &mut Criterion) {
    let mut group = c.benchmark_group("primitive_runtime_sort");
    let detected_tier = detect_profile();

    for len in [32usize, 256, 4096, 65_536] {
        group.throughput(Throughput::Elements(len as u64));

        let ints = build_int_values(len);
        group.bench_with_input(BenchmarkId::new("tagged_int_baseline", len), &ints, |b, source| {
            b.iter(|| {
                let mut values = source.clone();
                tagged_int_sort(&mut values);
                black_box(values);
            });
        });
        group.bench_with_input(BenchmarkId::new("primitive_int_scalar", len), &ints, |b, source| {
            b.iter(|| {
                let mut values = source.clone();
                black_box(sort_runtime_values(&mut values, SimdTier::Scalar));
                black_box(values);
            });
        });
        group.bench_with_input(BenchmarkId::new("primitive_int_auto", len), &ints, |b, source| {
            b.iter(|| {
                let mut values = source.clone();
                black_box(sort_runtime_values(&mut values, detected_tier));
                black_box(values);
            });
        });

        let floats = build_float_values(len);
        group.bench_with_input(BenchmarkId::new("tagged_float_baseline", len), &floats, |b, source| {
            b.iter(|| {
                let mut values = source.clone();
                tagged_float_sort(&mut values);
                black_box(values);
            });
        });
        group.bench_with_input(BenchmarkId::new("primitive_float_scalar", len), &floats, |b, source| {
            b.iter(|| {
                let mut values = source.clone();
                black_box(sort_runtime_values(&mut values, SimdTier::Scalar));
                black_box(values);
            });
        });
        group.bench_with_input(BenchmarkId::new("primitive_float_auto", len), &floats, |b, source| {
            b.iter(|| {
                let mut values = source.clone();
                black_box(sort_runtime_values_auto(&mut values));
                black_box(values);
            });
        });

        let bytes = build_byte_values(len);
        group.bench_with_input(BenchmarkId::new("tagged_byte_baseline", len), &bytes, |b, source| {
            b.iter(|| {
                let mut values = source.clone();
                tagged_byte_sort(&mut values);
                black_box(values);
            });
        });
        group.bench_with_input(BenchmarkId::new("primitive_byte_scalar", len), &bytes, |b, source| {
            b.iter(|| {
                let mut values = source.clone();
                black_box(sort_runtime_values(&mut values, SimdTier::Scalar));
                black_box(values);
            });
        });
        group.bench_with_input(BenchmarkId::new("primitive_byte_auto", len), &bytes, |b, source| {
            b.iter(|| {
                let mut values = source.clone();
                black_box(sort_runtime_values(&mut values, detected_tier));
                black_box(values);
            });
        });
    }

    group.finish();
}

criterion_group!(benches, bench_primitive_runtime_sort);
criterion_main!(benches);
