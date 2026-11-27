# Cranelift refusal propagation

Authored manual, not generated docgen output. The executable owner cases are
Rust tests in `src/compiler_rust/compiler/src/codegen/cranelift_error_latch_tests.rs`.
No Simple SSpec or new native compiler acceptance is claimed.

| Case | Required observable result |
| --- | --- |
| Conflicting declarations | Module finalization fails; emitting into an existing file returns false and preserves its bytes. |
| Missing imported function | Function completion returns zero; no finished function, builder backing or new output remains. |
| Invalid direct call and valid void call | The failing module is refused; a separate module retains a valid void call returning zero and emits a real object. |
| Concurrent independent modules | Failure does not spread between modules; free removes owned failure slots. |
| Isolated reset | An exact-name child process resets its own registry and confirms failure slots and unfinished builders are removed. |
| Missing call argument | A valid function reference with an invalid value handle refuses completion and module finalization. |
| Late module refusal | A function completed before the refusal cannot subsequently be defined. |

Seven normal owner cases passed with the default parallel runner; their ignored
reset helper executed alone in a checked child process. Eight existing
lifecycle/diagnostic cases also passed in a serial owner run (15 parent tests). See [scope and exact evidence](../../08_tracking/bug/cranelift_rejected_call_publication_2026_10_30.md).
