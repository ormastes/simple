# Live native-build worker timeout policy

| Field | Value |
|-------|-------|
| Source | `test/01_unit/app/io/process_ops_unlimited_timeout_spec.spl` |
| Scenarios | 3 |
| Runtime status | Not yet executed on the BSD self-hosted test runner |

The spec calls the actual `process_run_timeout_live` facade with `/bin/sh` children. It checks that timeout `0` permits a child to finish after a polling interval, a positive deadline kills a slower child and emits the timeout marker, and a negative input retains successful execution of a fast child through the legacy fallback branch.

The negative case does not wait 120 seconds, so it does not measure the fallback duration. The source policy keeps that mapping at 120000 ms; the BSD run will establish the child lifecycle behavior.
