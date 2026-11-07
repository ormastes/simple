# Installed Podman policy wrapper specification

Source: `test/01_unit/lib/nogc_async_mut/container/providers/linux/installed_policy_v3_spec.spl`.

Four authored cases, UNEXECUTED. Codec validity grants no endpoint trust or execution capability.

| Case | Oracle |
|---|---|
| Embedded compatibility | Wrapper roundtrip preserves exact existing V1 CLI bytes and digest. |
| Wrapper correlation | Endpoint/store changes alter wrapper digest; unsupported API version refuses. |
| Strict boundary | URI/network/relative/noncanonical/overlong paths, wrong UID, duplicate/unknown/wrong-type/noncanonical fields refuse. |
| Existing inventory | A legal32-option CLI record beyond64KiB survives the larger wrapper bound unchanged. |

Actual native endpoint/peer/store observation, owned/quarantined factory and live HTTP probing are pending. No build or check was performed.
