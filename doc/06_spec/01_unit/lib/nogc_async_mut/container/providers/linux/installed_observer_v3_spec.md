# Installed service probe source specification

Source: `test/01_unit/lib/nogc_async_mut/container/providers/linux/installed_observer_v3_spec.spl`.

Five authored scenarios, UNEXECUTED. Pure CLI/peer values are synthetic correlation data, not native observation or factory capability. Native positive probe acceptance is NOT_RUN; root allocation and native fork-origin-fence review are required.

| Scenario | Oracle |
|---|---|
| Exact correlation | Distinct installed identity binds policy, stable CLI and same-response API while retaining unchanged CLI identity. |
| Stable versus dynamic | Peer PID/GID/device/inode change identity; dynamic counts/time preserve stable identity but change evidence. |
| Service mismatch | API/body/CLI versions, store roots/driver, rootless and remote mismatches refuse. |
| Peer/time bounds | Wrong UID, invalid GID/PID/device/inode/time refuse; exact native2^60-1 boundary accepts as data and boundary+1 refuses. |
| Pre-I/O guards | One checked monotonic deadline rejects bad clocks/timeouts/overflow; actual probe rejects invalid policy with neither connection nor observation. |

Actual source uses canonical Unix owner, fixed deadline, complete bounded EOF and close-before-publish. Native timeout/partial-write/close/fork paths still require real acceptance evidence; no source-only assertion reports those paths passed.
