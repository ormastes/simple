# SFFI Family Convention Inference Engine — Pure Logic Tests

> Tests cover both:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SFFI Family Convention Inference Engine — Pure Logic Tests

Tests cover both:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/resource/resource_family_inference_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

**WP-D:** Convention inference engine (pure logic, no compiler wiring)

Tests cover both:
- Happy path: families that infer cleanly
- Ambiguous/degenerate cases that MUST return "cannot infer" (fail-closed rules)

The engine classifies families by verb patterns alone: acquire (open, create, new,
alloc, acquire, copy, clone), release (close, destroy, free, release, unref,
dispose), retain (retain, ref, add_ref).

Fail-closed rules:
1. Ambiguous/duplicate destructor → error
2. No recognized release fn → error (do NOT auto-create owning resource)
3. Multiple candidate receiver params → error (require explicit annotation)

## Scenarios

### resource family convention inference

#### infers rt_file_* family with clear acquire/release

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- infers rt_file_* family with clear acquire/release
   - Expected: result.is_success() is true
   - Expected: true is false
   - Expected: verb equals `open`
   - Expected: true is false
   - Expected: verb equals `close`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("infers rt_file_* family with clear acquire/release")
val result = resource_families.infer_family_conventions("rt_file", [
    "rt_file_open",
    "rt_file_read",
    "rt_file_write",
    "rt_file_close",
])

expect(result.is_success()).to_equal(true)
match result.acquire_verb:
    case nil:
        expect(true).to_equal(false)
    case verb:
        expect(verb).to_equal("open")
match result.release_verb:
    case nil:
        expect(true).to_equal(false)
    case verb:
        expect(verb).to_equal("close")
```

</details>

#### infers rt_image_* with load acquire, free release

- infers rt_image_* with load acquire, free release
   - Expected: result.is_success() is true
   - Expected: true is false
   - Expected: verb equals `load`
   - Expected: true is false
   - Expected: verb equals `free`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("infers rt_image_* with load acquire, free release")
val result = resource_families.infer_family_conventions("rt_image", [
    "rt_image_load",
    "rt_image_width",
    "rt_image_height",
    "rt_image_free",
])

expect(result.is_success()).to_equal(true)
match result.acquire_verb:
    case nil:
        expect(true).to_equal(false)
    case verb:
        expect(verb).to_equal("load")
match result.release_verb:
    case nil:
        expect(true).to_equal(false)
    case verb:
        expect(verb).to_equal("free")
```

</details>

#### fails-closed: two release verbs is ambiguous, never guess

- fails-closed: two release verbs is ambiguous, never guess
   - Expected: result.is_success() is false
   - Expected: true is false
   - Expected: err contains `ambiguous_destructor`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails-closed: two release verbs is ambiguous, never guess")
val result = resource_families.infer_family_conventions("rt_ambig", [
    "rt_ambig_create",
    "rt_ambig_close",
    "rt_ambig_free",
    "rt_ambig_read",
])

expect(result.is_success()).to_equal(false)
match result.error:
    case nil:
        expect(true).to_equal(false)
    case err:
        expect(err.contains("ambiguous_destructor")).to_equal(true)
```

</details>

#### fails-closed: no release verb errors, doesn't auto-create owning resource

- fails-closed: no release verb errors, doesn't auto-create owning resource
   - Expected: result.is_success() is false
   - Expected: true is false
   - Expected: err contains `no_release_verb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails-closed: no release verb errors, doesn't auto-create owning resource")
val result = resource_families.infer_family_conventions("rt_norelease", [
    "rt_norelease_create",
    "rt_norelease_read",
    "rt_norelease_write",
])

expect(result.is_success()).to_equal(false)
match result.error:
    case nil:
        expect(true).to_equal(false)
    case err:
        expect(err.contains("no_release_verb")).to_equal(true)
```

</details>

#### classifies retain/release pair for foreign RC candidate

- classifies retain/release pair for foreign RC candidate
   - Expected: result.is_success() is true
   - Expected: true is false
   - Expected: verb equals `retain`
   - Expected: true is false
   - Expected: verb equals `release`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("classifies retain/release pair for foreign RC candidate")
val result = resource_families.infer_family_conventions("rt_cuda_primary_ctx", [
    "rt_cuda_primary_ctx_retain",
    "rt_cuda_primary_ctx_release",
])

expect(result.is_success()).to_equal(true)
match result.retain_verb:
    case nil:
        expect(true).to_equal(false)
    case verb:
        expect(verb).to_equal("retain")
match result.release_verb:
    case nil:
        expect(true).to_equal(false)
    case verb:
        expect(verb).to_equal("release")
```

</details>

#### picks first acquire verb when multiple candidates exist

- picks first acquire verb when multiple candidates exist
   - Expected: result.is_success() is true
   - Expected: true is false
   - Expected: verb equals `new`
   - Expected: true is false
   - Expected: verb equals `free`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("picks first acquire verb when multiple candidates exist")
val result = resource_families.infer_family_conventions("rt_data", [
    "rt_data_new",
    "rt_data_create",
    "rt_data_process",
    "rt_data_free",
])

expect(result.is_success()).to_equal(true)
match result.acquire_verb:
    case nil:
        expect(true).to_equal(false)
    case verb:
        expect(verb).to_equal("new")
match result.release_verb:
    case nil:
        expect(true).to_equal(false)
    case verb:
        expect(verb).to_equal("free")
```

</details>

#### classifies mixed acquire/method/release functions

- classifies mixed acquire/method/release functions
   - Expected: result.is_success() is true
   - Expected: result.functions.len() equals `4`
   - Expected: send_fn.verb equals `send`
   - Expected: send_fn.category equals `method`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("classifies mixed acquire/method/release functions")
val result = resource_families.infer_family_conventions("rt_socket", [
    "rt_socket_create",
    "rt_socket_send",
    "rt_socket_recv",
    "rt_socket_close",
])

expect(result.is_success()).to_equal(true)
expect(result.functions.len()).to_equal(4)

val send_fn = result.functions[1]
expect(send_fn.verb).to_equal("send")
expect(send_fn.category).to_equal("method")
```

</details>

#### empty family fails (no release verb)

- empty family fails (no release verb)
   - Expected: result.is_success() is false
   - Expected: true is false
   - Expected: err contains `no_release_verb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("empty family fails (no release verb)")
val result = resource_families.infer_family_conventions("rt_empty", [])

expect(result.is_success()).to_equal(false)
match result.error:
    case nil:
        expect(true).to_equal(false)
    case err:
        expect(err.contains("no_release_verb")).to_equal(true)
```

</details>

#### only-methods family fails (no release)

- only-methods family fails (no release)
   - Expected: result.is_success() is false
   - Expected: true is false
   - Expected: err contains `no_release_verb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("only-methods family fails (no release)")
val result = resource_families.infer_family_conventions("rt_onlymethod", [
    "rt_onlymethod_read",
    "rt_onlymethod_write",
    "rt_onlymethod_flush",
])

expect(result.is_success()).to_equal(false)
match result.error:
    case nil:
        expect(true).to_equal(false)
    case err:
        expect(err.contains("no_release_verb")).to_equal(true)
```

</details>

#### strips family prefix correctly from function names

- strips family prefix correctly from function names
   - Expected: result.is_success() is true
   - Expected: true is false
   - Expected: verb equals `create`
   - Expected: true is false
   - Expected: verb equals `destroy`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("strips family prefix correctly from function names")
val result = resource_families.infer_family_conventions("rt_http_client", [
    "rt_http_client_create",
    "rt_http_client_send_request",
    "rt_http_client_destroy",
])

expect(result.is_success()).to_equal(true)
match result.acquire_verb:
    case nil:
        expect(true).to_equal(false)
    case verb:
        expect(verb).to_equal("create")
match result.release_verb:
    case nil:
        expect(true).to_equal(false)
    case verb:
        expect(verb).to_equal("destroy")
```

</details>

#### recognizes validity verbs but does not confuse with acquire/release

- recognizes validity verbs but does not confuse with acquire/release
   - Expected: result.is_success() is true
   - Expected: true is false
   - Expected: verb equals `alloc`
   - Expected: true is false
   - Expected: verb equals `free`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("recognizes validity verbs but does not confuse with acquire/release")
val result = resource_families.infer_family_conventions("rt_buffer", [
    "rt_buffer_alloc",
    "rt_buffer_is_valid",
    "rt_buffer_valid",
    "rt_buffer_free",
])

expect(result.is_success()).to_equal(true)
match result.acquire_verb:
    case nil:
        expect(true).to_equal(false)
    case verb:
        expect(verb).to_equal("alloc")
match result.release_verb:
    case nil:
        expect(true).to_equal(false)
    case verb:
        expect(verb).to_equal("free")
```

</details>

#### census sample: CudaContext (create/destroy)

- census sample: CudaContext (create/destroy)
   - Expected: result.is_success() is true
   - Expected: true is false
   - Expected: verb equals `create`
   - Expected: true is false
   - Expected: verb equals `destroy`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("census sample: CudaContext (create/destroy)")
val result = resource_families.infer_family_conventions("rt_cuda_ctx", [
    "rt_cuda_ctx_create",
    "rt_cuda_ctx_set_current",
    "rt_cuda_ctx_synchronize",
    "rt_cuda_ctx_destroy",
])

expect(result.is_success()).to_equal(true)
match result.acquire_verb:
    case nil:
        expect(true).to_equal(false)
    case verb:
        expect(verb).to_equal("create")
match result.release_verb:
    case nil:
        expect(true).to_equal(false)
    case verb:
        expect(verb).to_equal("destroy")
```

</details>

#### census sample: TorchTensor (new/free)

- census sample: TorchTensor (new/free)
   - Expected: result.is_success() is true
   - Expected: true is false
   - Expected: verb equals `new`
   - Expected: true is false
   - Expected: verb equals `free`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("census sample: TorchTensor (new/free)")
val result = resource_families.infer_family_conventions("rt_torch_torchtensor", [
    "rt_torch_torchtensor_new",
    "rt_torch_torchtensor_size",
    "rt_torch_torchtensor_data",
    "rt_torch_torchtensor_free",
])

expect(result.is_success()).to_equal(true)
match result.acquire_verb:
    case nil:
        expect(true).to_equal(false)
    case verb:
        expect(verb).to_equal("new")
match result.release_verb:
    case nil:
        expect(true).to_equal(false)
    case verb:
        expect(verb).to_equal("free")
```

</details>

#### deduplicates identical release verbs (not ambiguous)

- deduplicates identical release verbs (not ambiguous)
   - Expected: result.is_success() is true
   - Expected: true is false
   - Expected: verb equals `close`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("deduplicates identical release verbs (not ambiguous)")
val result = resource_families.infer_family_conventions("rt_dup", [
    "rt_dup_open",
    "rt_dup_close",
    "rt_dup_close",
])

expect(result.is_success()).to_equal(true)
match result.release_verb:
    case nil:
        expect(true).to_equal(false)
    case verb:
        expect(verb).to_equal("close")
```

</details>

#### detects foreign RC candidate (has acquire, release, and retain)

- detects foreign RC candidate (has acquire, release, and retain)
   - Expected: result.is_success() is true
   - Expected: rc_result.is_candidate is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("detects foreign RC candidate (has acquire, release, and retain)")
val result = resource_families.infer_family_conventions("rt_cuda_primary_ctx", [
    "rt_cuda_primary_ctx_acquire",
    "rt_cuda_primary_ctx_retain",
    "rt_cuda_primary_ctx_release",
])

expect(result.is_success()).to_equal(true)
val rc_result = resource_families.classify_rc_strategy(result)
expect(rc_result.is_candidate).to_equal(true)
```

</details>

#### not an RC candidate without retain (unique ownership)

- not an RC candidate without retain (unique ownership)
   - Expected: result.is_success() is true
   - Expected: rc_result.is_candidate is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("not an RC candidate without retain (unique ownership)")
val result = resource_families.infer_family_conventions("rt_file", [
    "rt_file_open",
    "rt_file_close",
])

expect(result.is_success()).to_equal(true)
val rc_result = resource_families.classify_rc_strategy(result)
expect(rc_result.is_candidate).to_equal(false)
```

</details>

#### reports all unique release verbs when ambiguous

- reports all unique release verbs when ambiguous
   - Expected: result.is_success() is false
   - Expected: result.release_verbs_found.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports all unique release verbs when ambiguous")
val result = resource_families.infer_family_conventions("rt_multi", [
    "rt_multi_create",
    "rt_multi_close",
    "rt_multi_free",
    "rt_multi_destroy",
    "rt_multi_free",
    "rt_multi_close",
])

expect(result.is_success()).to_equal(false)
expect(result.release_verbs_found.len()).to_equal(3)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `989f37a6e2caf18cb183af44e55385f871698d610296222112f1ba4412563511`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `989f37a6e2caf18cb183af44e55385f871698d610296222112f1ba4412563511`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `989f37a6e2caf18cb183af44e55385f871698d610296222112f1ba4412563511`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/resource/resource_family_inference_spec.spl
mirror: doc/06_spec/01_unit/compiler/resource/resource_family_inference_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/resource/resource_family_inference_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/resource/resource_family_inference_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/resource/resource_family_inference_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/resource/resource_family_inference_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'infers rt_file_* family with clear acquire/release' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/resource/resource_family_inference_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'infers rt_image_* with load acquire, free release' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/resource/resource_family_inference_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails-closed: two release verbs is ambiguous, never guess' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
