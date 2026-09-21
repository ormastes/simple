.text
# The retained Phase 2 backend emits callback-field calls under these ABI
# labels. Route them to the harness callbacks so the production arena body is
# exercised rather than a generated nil stub.
.globl _RtHalIsolatedHostPort.current_owner_fn
_RtHalIsolatedHostPort.current_owner_fn:
    mov x0, #41
    ret
.globl _RtHalIsolatedHostPort.bind_adapter_fn
_RtHalIsolatedHostPort.bind_adapter_fn:
    mov x0, #1
    ret
.globl _RtHalIsolatedHostPort.cancel_and_reap_fn
_RtHalIsolatedHostPort.cancel_and_reap_fn:
    mov x0, #1
    ret
.globl _RtHalIsolatedHostPort.close_fn
_RtHalIsolatedHostPort.close_fn:
    b _build__test__llvm_actual_join_close_path__arena_actual_copy__fixture_close_fails
.globl _RtHalIsolatedHostPort.spawn_compare_exact_fn
_RtHalIsolatedHostPort.spawn_compare_exact_fn:
    mov x0, #73
    ret
.globl _RtHalIsolatedHostPort.spawn_replay_exact_fn
_RtHalIsolatedHostPort.spawn_replay_exact_fn:
    mov x0, #73
    ret
.globl _RtHalIsolatedHostPort.join_exact_until_fn
_RtHalIsolatedHostPort.join_exact_until_fn:
    b _build__test__llvm_actual_join_close_path__arena_actual_copy__fixture_joined
.globl _RtHalIsolatedHostPort.shutdown_fn
_RtHalIsolatedHostPort.shutdown_fn:
    mov x0, #1
    ret
