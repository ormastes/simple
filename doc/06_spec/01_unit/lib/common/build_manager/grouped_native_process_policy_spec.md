# Grouped native process and disk admission

Executable: `test/01_unit/lib/common/build_manager/grouped_native_process_policy_spec.spl`.

The existing memory cases require full active process caps plus host reserve,
independently check Windows commit headroom, enforce CPU capacity, and reject
unmeasured fabricated commit values or active charges beyond their limits.

The disk cases call the production shared budget decision used by singleton and
wave admission, asserting its `admitted` and `required_bytes` fields. They do not
reimplement the capacity decision in the test. Arithmetic failure cases exercise
the checked requirement helper and its propagation through the decision owner:

| Scenario | Required outcome |
|---|---|
| Empty source, 8.5 GiB reserve, 2 GiB estimated growth | 10.5 GiB requirement; reserve alone and one byte below requirement do not fit |
| 20 GiB reserve, 1 GiB source at 8x allowance, 2 GiB estimated growth | 30 GiB requirement; 25 GiB does not fit; equality fits |
| Active groups plus candidate | Add active growth once and retain the reserve once |
| Zero-valued arithmetic inputs | Zero requirement |
| Negative available capacity, reserve, active growth, source size or estimate | Explicit invalid-input error |
| Source multiplication or any subsequent addition overflows i64 | Explicit overflow error, never a wrapped admission |
| Exact i64 maximum from each valid input arrangement | Accepted without overflow |

Run once with an admitted self-hosted runtime:

```text
<admitted-runtime> test test/01_unit/lib/common/build_manager/grouped_native_process_policy_spec.spl
```

Status for the singleton reserve correction: new SSpec cases UNRUN. No admitted
general test runtime was available when the candidate was prepared; a
hello-qualified bootstrap compiler does not establish test-runner admission.
Static/source review cannot substitute for executable acceptance. No production
deployment or manager retry is authorized by this manual.
