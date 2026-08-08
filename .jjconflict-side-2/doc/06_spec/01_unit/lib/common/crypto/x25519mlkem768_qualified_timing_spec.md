# X25519mlkem768 Qualified Timing Specification

> Tests covering X25519MLKEM768 qualified raw timing receipts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Qualified Timing Specification

## Scenarios

### X25519MLKEM768 qualified raw timing receipts

#### admits role-fixed scalar and AVX2 samples and derives every aggregate

- Bind measurements to an admitted backend matrix
- Admit two untimed full-operation warmups
- Admit thirty ordered full-operation samples
- qualification, scalar warm,  timing samples
- qualification, candidate warm,  timing samples
   - Expected: x25519_mlkem768_timing_p50_us(candidate_timed) equals `114`
   - Expected: x25519_mlkem768_timing_p95_us(candidate_timed) equals `128`
   - Expected: x25519_mlkem768_timing_p99_us(candidate_timed) equals `129`


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Bind measurements to an admitted backend matrix")
val qualification =
    _QUALIFICATION_AVX2
val scalar_warm = _warm_receipt(
    qualification, X25519MlKem768TimingRole.ScalarReference)
val candidate_warm = _warm_receipt(
    qualification, X25519MlKem768TimingRole.Candidate)

step("Admit two untimed full-operation warmups")
expect(x25519_mlkem768_admit_warm_setup(
    qualification, scalar_warm).is_ok()).to_be(true)
expect(x25519_mlkem768_admit_warm_setup(
    qualification, candidate_warm).is_ok()).to_be(true)

step("Admit thirty ordered full-operation samples")
val scalar_timed = _timed_receipt(
    qualification, scalar_warm, _timing_samples(200000))
val candidate_timed = _timed_receipt(
    qualification, candidate_warm, _timing_samples(100000))
val schedule = x25519_mlkem768_synthetic_paired_schedule(
    qualification, scalar_timed, candidate_timed)
expect(x25519_mlkem768_admit_timed_operations(
    qualification, scalar_warm, scalar_timed).is_ok()).to_be(true)
expect(x25519_mlkem768_admit_timed_operations(
    qualification, candidate_warm, candidate_timed).is_ok()).to_be(true)
expect(x25519_mlkem768_admit_paired_schedule(
    qualification, scalar_warm, candidate_warm,
    scalar_timed, candidate_timed,
    schedule).is_ok()).to_be(true)
expect(x25519_mlkem768_timing_p50_us(candidate_timed)).to_equal(114)
expect(x25519_mlkem768_timing_p95_us(candidate_timed)).to_equal(128)
expect(x25519_mlkem768_timing_p99_us(candidate_timed)).to_equal(129)
expect(x25519_mlkem768_timing_operations_per_second(
    candidate_timed)).to_equal(26200)
expect(x25519_mlkem768_qualified_timing_sha256(
    qualification, scalar_warm, candidate_warm,
    scalar_timed, candidate_timed, schedule).len()).to_equal(64)
```

</details>

#### rejects malformed, misordered, overlapping, or rebound paired schedules

- qualification, scalar warm,  timing samples
- qualification, candidate warm,  timing samples
- qualification, scalar warm,  timing samples
- short schedule =  rehash schedule
- wrong base =  rehash schedule
-  timing sample count
-  timing sample count
- even overlap =  rehash schedule
- odd overlap =  rehash schedule
- wrong duration =  rehash schedule
- pair overlap =  rehash schedule
- rebound =  rehash schedule


<details>
<summary>Executable SSpec</summary>

Runnable source: 125 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val qualification =
    _QUALIFICATION_AVX2
val scalar_warm = _warm_receipt(
    qualification, X25519MlKem768TimingRole.ScalarReference)
val candidate_warm = _warm_receipt(
    qualification, X25519MlKem768TimingRole.Candidate)
val scalar_timed = _timed_receipt(
    qualification, scalar_warm, _timing_samples(200000))
val candidate_timed = _timed_receipt(
    qualification, candidate_warm, _timing_samples(100000))
val valid = x25519_mlkem768_synthetic_paired_schedule(
    qualification, scalar_timed, candidate_timed)

var forged_hash = valid
forged_hash.receipt_sha256 = "0" * 64
expect(x25519_mlkem768_admit_paired_schedule(
    qualification, scalar_warm, candidate_warm,
    scalar_timed, candidate_timed,
    forged_hash).unwrap_err()).to_equal(
    "paired-schedule-receipt-invalid")

var stale_scalar = _timed_receipt(
    qualification, scalar_warm, _timing_samples(200000))
stale_scalar.samples_ns[0] = stale_scalar.samples_ns[0] + 1
expect(x25519_mlkem768_admit_paired_schedule(
    qualification, scalar_warm, candidate_warm,
    stale_scalar, candidate_timed,
    valid).unwrap_err()).to_equal(
    "paired-schedule-scalar-timed-invalid")

var short_schedule = valid
val empty_starts: [i64] = []
short_schedule.scalar_started_ns = empty_starts
short_schedule = _rehash_schedule(short_schedule)
expect(x25519_mlkem768_admit_paired_schedule(
    qualification, scalar_warm, candidate_warm,
    scalar_timed, candidate_timed,
    short_schedule).unwrap_err()).to_equal(
    "paired-schedule-count-invalid")

var wrong_base = valid
wrong_base.ordinal_base = 1
wrong_base = _rehash_schedule(wrong_base)
expect(x25519_mlkem768_admit_paired_schedule(
    qualification, scalar_warm, candidate_warm,
    scalar_timed, candidate_timed,
    wrong_base).unwrap_err()).to_equal("paired-schedule-count-invalid")

val odd_scalar = _timed_receipt(
    qualification, scalar_warm,
    _timing_sample_count(31, 200000))
val odd_candidate = _timed_receipt(
    qualification, candidate_warm,
    _timing_sample_count(31, 100000))
val odd_count = x25519_mlkem768_synthetic_paired_schedule(
    qualification, odd_scalar, odd_candidate)
expect(x25519_mlkem768_admit_paired_schedule(
    qualification, scalar_warm, candidate_warm,
    odd_scalar, odd_candidate, odd_count).unwrap_err()).to_equal(
    "paired-schedule-count-invalid")

var even_overlap = x25519_mlkem768_synthetic_paired_schedule(
    qualification, scalar_timed, candidate_timed)
even_overlap.candidate_started_ns[0] =
    even_overlap.scalar_finished_ns[0] - 1
even_overlap.candidate_finished_ns[0] =
    even_overlap.candidate_started_ns[0] +
        candidate_timed.samples_ns[0]
even_overlap = _rehash_schedule(even_overlap)
expect(x25519_mlkem768_admit_paired_schedule(
    qualification, scalar_warm, candidate_warm,
    scalar_timed, candidate_timed,
    even_overlap).unwrap_err()).to_equal(
    "paired-schedule-abba-order-invalid")

var odd_overlap = x25519_mlkem768_synthetic_paired_schedule(
    qualification, scalar_timed, candidate_timed)
odd_overlap.scalar_started_ns[1] =
    odd_overlap.candidate_finished_ns[1] - 1
odd_overlap.scalar_finished_ns[1] = odd_overlap.scalar_started_ns[1] +
    scalar_timed.samples_ns[1]
odd_overlap = _rehash_schedule(odd_overlap)
expect(x25519_mlkem768_admit_paired_schedule(
    qualification, scalar_warm, candidate_warm,
    scalar_timed, candidate_timed,
    odd_overlap).unwrap_err()).to_equal(
    "paired-schedule-abba-order-invalid")

var wrong_duration = x25519_mlkem768_synthetic_paired_schedule(
    qualification, scalar_timed, candidate_timed)
wrong_duration.scalar_finished_ns[0] =
    wrong_duration.scalar_finished_ns[0] + 1
wrong_duration = _rehash_schedule(wrong_duration)
expect(x25519_mlkem768_admit_paired_schedule(
    qualification, scalar_warm, candidate_warm,
    scalar_timed, candidate_timed,
    wrong_duration).unwrap_err()).to_equal(
    "paired-schedule-duration-invalid")

var pair_overlap = x25519_mlkem768_synthetic_paired_schedule(
    qualification, scalar_timed, candidate_timed)
pair_overlap.candidate_started_ns[1] =
    valid.candidate_started_ns[0]
pair_overlap.candidate_finished_ns[1] =
    pair_overlap.candidate_started_ns[1] +
        candidate_timed.samples_ns[1]
pair_overlap.scalar_started_ns[1] =
    pair_overlap.candidate_finished_ns[1] + 1000
pair_overlap.scalar_finished_ns[1] = pair_overlap.scalar_started_ns[1] +
    scalar_timed.samples_ns[1]
pair_overlap = _rehash_schedule(pair_overlap)
expect(x25519_mlkem768_admit_paired_schedule(
    qualification, scalar_warm, candidate_warm,
    scalar_timed, candidate_timed,
    pair_overlap).unwrap_err()).to_equal(
    "paired-schedule-overlap-invalid")

var rebound = valid
rebound.session_id = "different-session"
rebound = _rehash_schedule(rebound)
expect(x25519_mlkem768_admit_paired_schedule(
    qualification, scalar_warm, candidate_warm,
    scalar_timed, candidate_timed,
    rebound).unwrap_err()).to_equal(
    "paired-schedule-binding-mismatch")
```

</details>

#### rejects forged warmup hashes, role counts, and timed setup

- Reject setup, fallback, kernel-only, or mismatch contamination
- wrong counts =  rehash warm
- one candidate warmup =  rehash warm
- timed setup =  rehash warm


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject setup, fallback, kernel-only, or mismatch contamination")
val qualification =
    _QUALIFICATION_NEON
var forged = _warm_receipt(
    qualification, X25519MlKem768TimingRole.Candidate)
forged.receipt_sha256 = "0" * 64
match x25519_mlkem768_admit_warm_setup(qualification, forged):
    case Err(reason): expect(reason).to_equal(
        "warm-setup-receipt-invalid")
    case Ok(_): fail("forged warmup hash was admitted")
var wrong_counts = _warm_receipt(
    qualification, X25519MlKem768TimingRole.Candidate)
wrong_counts.scalar_qualification_count = 2
wrong_counts = _rehash_warm(wrong_counts)
match x25519_mlkem768_admit_warm_setup(qualification, wrong_counts):
    case Err(reason): expect(reason).to_equal(
        "warm-setup-count-invalid")
    case Ok(_): fail("wrong warmup role counts were admitted")
var one_candidate_warmup = _warm_receipt(
    qualification, X25519MlKem768TimingRole.Candidate)
one_candidate_warmup.completed_full_exchanges = 2
one_candidate_warmup.candidate_warmup_count = 1
one_candidate_warmup = _rehash_warm(one_candidate_warmup)
match x25519_mlkem768_admit_warm_setup(
        qualification, one_candidate_warmup):
    case Err(reason): expect(reason).to_equal(
        "warm-setup-count-invalid")
    case Ok(_): fail("single candidate warmup was admitted")
var timed_setup = _warm_receipt(
    qualification, X25519MlKem768TimingRole.Candidate)
timed_setup.setup_operations_timed = 1
timed_setup = _rehash_warm(timed_setup)
match x25519_mlkem768_admit_warm_setup(qualification, timed_setup):
    case Err(reason): expect(reason).to_equal("warm-setup-contaminated")
    case Ok(_): fail("timed setup was admitted as warmup")
```

</details>

#### rejects short, reordered, miscounted, and contaminated sample sets

- short samples push
   - Expected: x25519_mlkem768_timing_p50_us(short_receipt) equals `0`
- qualification, warm,  timing sample count
- qualification, warm,  timing samples
- qualification, warm,  timing samples
- miscounted =  rehash timed
- qualification, warm,  timing samples
- contaminated =  rehash timed


<details>
<summary>Executable SSpec</summary>

Runnable source: 56 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val qualification =
    _QUALIFICATION_RVV
val warm = _warm_receipt(
    qualification, X25519MlKem768TimingRole.Candidate)
var short_samples: [i64] = []
var index: i64 = 0
while index < 29:
    short_samples.push(100000 + index)
    index = index + 1
val short_receipt = _timed_receipt(
    qualification, warm, short_samples)
match x25519_mlkem768_admit_timed_operations(
        qualification, warm, short_receipt):
    case Err(reason): expect(reason).to_equal(
        "timed-operation-samples-invalid")
    case Ok(_): fail("short sample set was admitted")
expect(x25519_mlkem768_timing_p50_us(short_receipt)).to_equal(0)
expect(x25519_mlkem768_timing_operations_per_second(
    short_receipt)).to_equal(0)

val oversized_receipt = _timed_receipt(
    qualification, warm, _timing_sample_count(1025, 100000))
match x25519_mlkem768_admit_timed_operations(
        qualification, warm, oversized_receipt):
    case Err(reason): expect(reason).to_equal(
        "timed-operation-samples-invalid")
    case Ok(_): fail("1,025-sample set was admitted")

var reordered = _timed_receipt(
    qualification, warm, _timing_samples(100000))
reordered.samples_ns[0] = reordered.samples_ns[1]
match x25519_mlkem768_admit_timed_operations(
        qualification, warm, reordered):
    case Err(reason): expect(reason).to_equal(
        "timed-operation-receipt-invalid")
    case Ok(_): fail("mutated ordered samples retained an old receipt")

var miscounted = _timed_receipt(
    qualification, warm, _timing_samples(100000))
miscounted.hybrid_operation_count = 89
miscounted = _rehash_timed(miscounted)
match x25519_mlkem768_admit_timed_operations(
        qualification, warm, miscounted):
    case Err(reason): expect(reason).to_equal(
        "timed-operation-count-invalid")
    case Ok(_): fail("miscounted hybrid operations were admitted")

var contaminated = _timed_receipt(
    qualification, warm, _timing_samples(100000))
contaminated.fallback_operations = 1
contaminated = _rehash_timed(contaminated)
match x25519_mlkem768_admit_timed_operations(
        qualification, warm, contaminated):
    case Err(reason): expect(reason).to_equal(
        "timed-operation-contaminated")
    case Ok(_): fail("fallback-contaminated timing was admitted")
```

</details>

#### rejects rehashed timed binding and exchange-count mutations

- qualification, warm,  timing samples
- rebound =  rehash timed
- qualification, warm,  timing samples
- wrong exchange count =  rehash timed


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val qualification =
    _QUALIFICATION_AVX2
val warm = _warm_receipt(
    qualification, X25519MlKem768TimingRole.Candidate)
var rebound = _timed_receipt(
    qualification, warm, _timing_samples(100000))
rebound.session_id = "different-timed-session"
rebound = _rehash_timed(rebound)
match x25519_mlkem768_admit_timed_operations(
        qualification, warm, rebound):
    case Err(reason): expect(reason).to_equal(
        "timed-operation-binding-mismatch")
    case Ok(_): fail("rebound timed session was admitted")

var wrong_exchange_count = _timed_receipt(
    qualification, warm, _timing_samples(100000))
wrong_exchange_count.full_exchange_count = 29
wrong_exchange_count.hybrid_operation_count = 87
wrong_exchange_count = _rehash_timed(wrong_exchange_count)
match x25519_mlkem768_admit_timed_operations(
        qualification, warm, wrong_exchange_count):
    case Err(reason): expect(reason).to_equal(
        "timed-operation-count-invalid")
    case Ok(_): fail("sample/exchange count mismatch was admitted")
```

</details>

#### requires complete multi-kernel GPU lifecycle counts

- qualification, warm,  timing samples
- qualification, warm,  timing samples
- missing readback =  rehash timed
- qualification, warm,  timing samples
- exchange substitution =  rehash timed
- qualification, warm,  timing samples
- kernel mismatch =  rehash timed


<details>
<summary>Executable SSpec</summary>

Runnable source: 50 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val qualification =
    _QUALIFICATION_VULKAN
val warm = _warm_receipt(
    qualification, X25519MlKem768TimingRole.Candidate)
var stale_v1_hash = _timed_receipt(
    qualification, warm, _timing_samples(100000))
stale_v1_hash.gpu_kernel_count =
    stale_v1_hash.gpu_kernel_count + 1
match x25519_mlkem768_admit_timed_operations(
        qualification, warm, stale_v1_hash):
    case Err(reason): expect(reason).to_equal(
        "timed-operation-receipt-invalid")
    case Ok(_): fail("unhashed GPU kernel count mutation was admitted")

var missing_readback = _timed_receipt(
    qualification, warm, _timing_samples(100000))
missing_readback.gpu_readback_count =
    missing_readback.gpu_kernel_count - 1
missing_readback = _rehash_timed(missing_readback)
match x25519_mlkem768_admit_timed_operations(
        qualification, warm, missing_readback):
    case Err(reason): expect(reason).to_equal(
        "timed-operation-backend-evidence-invalid")
    case Ok(_): fail("incomplete GPU lifecycle was admitted")

var exchange_substitution = _timed_receipt(
    qualification, warm, _timing_samples(100000))
val exchanges = exchange_substitution.full_exchange_count
exchange_substitution.gpu_transfer_count = exchanges
exchange_substitution.gpu_launch_count = exchanges
exchange_substitution.gpu_synchronization_count = exchanges
exchange_substitution.gpu_readback_count = exchanges
exchange_substitution.gpu_kernel_count = exchanges
exchange_substitution = _rehash_timed(exchange_substitution)
match x25519_mlkem768_admit_timed_operations(
        qualification, warm, exchange_substitution):
    case Err(reason): expect(reason).to_equal(
        "timed-operation-backend-evidence-invalid")
    case Ok(_): fail("one-launch-per-exchange substitution was admitted")

var kernel_mismatch = _timed_receipt(
    qualification, warm, _timing_samples(100000))
kernel_mismatch.gpu_kernel_count =
    kernel_mismatch.gpu_kernel_count + 1
kernel_mismatch = _rehash_timed(kernel_mismatch)
match x25519_mlkem768_admit_timed_operations(
        qualification, warm, kernel_mismatch):
    case Err(reason): expect(reason).to_equal(
        "timed-operation-backend-evidence-invalid")
    case Ok(_): fail("GPU lifecycle/kernel mismatch was admitted")
```

</details>

#### rejects invalid qualification and warm-session rebinding first

- rebound =  rehash warm


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var qualification =
    _QUALIFICATION_AVX2
val original_warm = _warm_receipt(
    qualification, X25519MlKem768TimingRole.Candidate)
qualification.qualification_sha256 = "0" * 64
match x25519_mlkem768_admit_warm_setup(
        qualification, original_warm):
    case Err(reason): expect(reason).to_equal(
        "measurement-qualification-invalid")
    case Ok(_): fail("invalid qualification admitted warmup")
val valid_qualification =
    _QUALIFICATION_AVX2
var rebound = _warm_receipt(
    valid_qualification, X25519MlKem768TimingRole.Candidate)
rebound.session_id = "different-session"
rebound = _rehash_warm(rebound)
match x25519_mlkem768_admit_warm_setup(
        valid_qualification, rebound):
    case Err(reason): expect(reason).to_equal(
        "warm-setup-binding-mismatch")
    case Ok(_): fail("rebound warmup session was admitted")
```

</details>

#### admits RVV only with observed VLEN and keeps scalar acceleration zero

- qualification, candidate warm,  timing samples
- no vlen =  rehash timed
- qualification, scalar warm,  timing samples
- accelerated scalar =  rehash timed
- qualification, scalar warm,  timing samples
- gpu claiming scalar =  rehash timed
- gpu claiming rvv =  rehash timed


<details>
<summary>Executable SSpec</summary>

Runnable source: 45 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val qualification =
    _QUALIFICATION_RVV
val candidate_warm = _warm_receipt(
    qualification, X25519MlKem768TimingRole.Candidate)
val candidate = _timed_receipt(
    qualification, candidate_warm, _timing_samples(100000))
expect(x25519_mlkem768_admit_timed_operations(
    qualification, candidate_warm, candidate).is_ok()).to_be(true)
var no_vlen = candidate
no_vlen.observed_rvv_vlen_bits = 0
no_vlen = _rehash_timed(no_vlen)
match x25519_mlkem768_admit_timed_operations(
        qualification, candidate_warm, no_vlen):
    case Err(reason): expect(reason).to_equal(
        "timed-operation-backend-evidence-invalid")
    case Ok(_): fail("RVV timing without VLEN was admitted")
val scalar_warm = _warm_receipt(
    qualification, X25519MlKem768TimingRole.ScalarReference)
var accelerated_scalar = _timed_receipt(
    qualification, scalar_warm, _timing_samples(200000))
accelerated_scalar.accelerated_operation_count = 1
accelerated_scalar = _rehash_timed(accelerated_scalar)
match x25519_mlkem768_admit_timed_operations(
        qualification, scalar_warm, accelerated_scalar):
    case Err(reason): expect(reason).to_equal(
        "timed-operation-backend-evidence-invalid")
    case Ok(_): fail("accelerated scalar timing was admitted")
var gpu_claiming_scalar = _timed_receipt(
    qualification, scalar_warm, _timing_samples(200000))
gpu_claiming_scalar.gpu_kernel_count = 1
gpu_claiming_scalar = _rehash_timed(gpu_claiming_scalar)
match x25519_mlkem768_admit_timed_operations(
        qualification, scalar_warm, gpu_claiming_scalar):
    case Err(reason): expect(reason).to_equal(
        "timed-operation-backend-evidence-invalid")
    case Ok(_): fail("scalar timing claimed a GPU kernel event")

var gpu_claiming_rvv = candidate
gpu_claiming_rvv.gpu_kernel_count = 1
gpu_claiming_rvv = _rehash_timed(gpu_claiming_rvv)
match x25519_mlkem768_admit_timed_operations(
        qualification, candidate_warm, gpu_claiming_rvv):
    case Err(reason): expect(reason).to_equal(
        "timed-operation-backend-evidence-invalid")
    case Ok(_): fail("SIMD timing claimed a GPU kernel event")
```

</details>

#### rejects AVX2 and NEON VLEN claims and incomplete SIMD evidence

- avx qualification, avx warm,  timing samples
- avx vlen =  rehash timed
- neon qualification, neon warm,  timing samples
- neon vlen =  rehash timed
- avx qualification, avx warm,  timing samples
- missing chunks =  rehash timed
- neon qualification, neon warm,  timing samples
- missing rss =  rehash timed
- neon qualification, neon warm,  timing samples
- forged rss =  rehash timed


<details>
<summary>Executable SSpec</summary>

Runnable source: 58 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val avx_qualification =
    _QUALIFICATION_AVX2
val avx_warm = _warm_receipt(
    avx_qualification, X25519MlKem768TimingRole.Candidate)
var avx_vlen = _timed_receipt(
    avx_qualification, avx_warm, _timing_samples(100000))
avx_vlen.observed_rvv_vlen_bits = 256
avx_vlen = _rehash_timed(avx_vlen)
match x25519_mlkem768_admit_timed_operations(
        avx_qualification, avx_warm, avx_vlen):
    case Err(reason): expect(reason).to_equal(
        "timed-operation-backend-evidence-invalid")
    case Ok(_): fail("AVX2 timing claimed an RVV VLEN")

val neon_qualification =
    _QUALIFICATION_NEON
val neon_warm = _warm_receipt(
    neon_qualification, X25519MlKem768TimingRole.Candidate)
var neon_vlen = _timed_receipt(
    neon_qualification, neon_warm, _timing_samples(100000))
neon_vlen.observed_rvv_vlen_bits = 128
neon_vlen = _rehash_timed(neon_vlen)
match x25519_mlkem768_admit_timed_operations(
        neon_qualification, neon_warm, neon_vlen):
    case Err(reason): expect(reason).to_equal(
        "timed-operation-backend-evidence-invalid")
    case Ok(_): fail("NEON timing claimed an RVV VLEN")

var missing_chunks = _timed_receipt(
    avx_qualification, avx_warm, _timing_samples(100000))
missing_chunks.simd_chunk_hits = 89
missing_chunks = _rehash_timed(missing_chunks)
match x25519_mlkem768_admit_timed_operations(
        avx_qualification, avx_warm, missing_chunks):
    case Err(reason): expect(reason).to_equal(
        "timed-operation-backend-evidence-invalid")
    case Ok(_): fail("incomplete AVX2 SIMD evidence was admitted")

var missing_rss = _timed_receipt(
    neon_qualification, neon_warm, _timing_samples(100000))
missing_rss.max_rss_kb = 0
missing_rss = _rehash_timed(missing_rss)
match x25519_mlkem768_admit_timed_operations(
        neon_qualification, neon_warm, missing_rss):
    case Err(reason): expect(reason).to_equal(
        "timed-operation-platform-observation-mismatch")
    case Ok(_): fail("timing without resident-set evidence was admitted")

var forged_rss = _timed_receipt(
    neon_qualification, neon_warm, _timing_samples(100000))
forged_rss.max_rss_kb =
    neon_qualification.platform_observation.peak_memory_kib + 1
forged_rss = _rehash_timed(forged_rss)
match x25519_mlkem768_admit_timed_operations(
        neon_qualification, neon_warm, forged_rss):
    case Err(reason): expect(reason).to_equal(
        "timed-operation-platform-observation-mismatch")
    case Ok(_): fail("forged resident-set evidence was admitted")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/x25519mlkem768_qualified_timing_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 qualified raw timing receipts.
- X25519MLKEM768 qualified raw timing receipts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
