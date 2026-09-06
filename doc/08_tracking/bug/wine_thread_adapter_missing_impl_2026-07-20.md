# Missing implementation: common.wine_thread_adapter module

- **Status:** OPEN
- **Discovered:** 2026-07-20, whole-suite triage campaign
- **Area:** `src/lib/common/` — Wine thread-adapter SFFI gate module
- **Severity:** Medium — the only consumer (its own spec) can never run;
  the module this spec targets does not exist anywhere in the repo.

## Symptom

`test/unit/lib/common/wine_thread_adapter_spec.spl` fails to even start:

```
error: semantic: Cannot resolve module: common.wine_thread_adapter
error: test-runner: no examples executed
```

## Root cause

The spec imports:

```spl
use common.wine_thread_adapter.{
    wine_thread_adapter_feature_string,
    wine_thread_adapter_gate,
    wine_thread_adapter_gate_with_wait_result,
    wine_thread_adapter_missing_apis,
    wine_thread_adapter_required_apis,
    wine_thread_adapter_sffi_binding
}
use common.wine_nt_thread_wait.{
    wine_nt_create_pending_thread,
    wine_nt_create_thread,
    wine_nt_thread_table_new,
    wine_nt_wait_for_single_object
}
```

`common.wine_nt_thread_wait` resolves fine (`src/lib/common/wine_nt_thread_wait.spl`
exists), but `common.wine_thread_adapter` does not — there is no
`wine_thread_adapter.spl` anywhere under `src/`, and none of the six imported
function names (`wine_thread_adapter_feature_string`,
`wine_thread_adapter_gate`, `wine_thread_adapter_gate_with_wait_result`,
`wine_thread_adapter_missing_apis`, `wine_thread_adapter_required_apis`,
`wine_thread_adapter_sffi_binding`) are defined anywhere in the codebase
(repo-wide grep for each `fn` signature returns nothing). `git log` on the
spec file's own history shows it landed via generic "hourly sync" / "wave-3"
sweep commits (`115803a7aff`, `bf40503e421`) rather than a dedicated feature
commit — consistent with the known "sync sweeps agent scratch state" failure
class (a parallel lane's in-progress spec got swept into `origin` by a
whole-working-copy sync commit before its companion implementation file was
ever written/landed).

Neighboring modules (`wine_kernel32_thread_wait.spl`,
`wine_nt_thread_wait.spl`, `wine_async_gate.spl`, `wine_host_gate.spl`,
`wine_posix_adapter.spl`, `wine_vm_adapter.spl`) cover related
thread/wait/gate concerns but none define the `wine_thread_adapter_*` API
surface this spec expects — this is not a simple rename fix.

## Failing command

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 \
  /home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple \
  test test/unit/lib/common/wine_thread_adapter_spec.spl --no-session-daemon
```

## Recommendation

Either (a) implement `src/lib/common/wine_thread_adapter.spl` with the six
functions the spec expects (an SFFI capability-gate over the Wine
thread/mutex/condvar API surface, judging by the imported names and the
spec's own assertions — `wine_thread_adapter_required_apis`,
`_missing_apis`, `_gate`, `_gate_with_wait_result`, `_feature_string`,
`_sffi_binding`), or (b) if this was scratch/WIP work from a different lane
that never shipped, remove the dead spec — that decision belongs to the
feature owner, not this triage pass. Nothing in the spec was weakened here.
