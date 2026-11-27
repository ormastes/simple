# Bootstrap host reserve requirements

Scope: the user's selected bootstrap bug-fix work on `release/1.0.0`; restore
the existing host reserve contract without introducing a new resource policy.

| Requirement | Acceptance | Evidence |
|---|---|---|
| REQ-HR-01 | Known host free memory is reduced by the host reserve, then bounded by positive declared and enforced compiler caps. | Native fixture cases 1–4 and 8; SSpec known-host-free scenarios. |
| REQ-HR-02 | A roomy host with a 24 GiB compiler cap does not lose that entire cap to the separate 24 GiB host reserve. | Native case 1 uses exact mirgen2 inputs. |
| REQ-HR-03 | Unknown host free preserves the conservative fallback; absent cap uses known free; no measurements invent no capacity. | Native cases 5–7; existing SSpec fallback scenarios. |
| REQ-HR-04 | Enforced caps, coordinator reservation, worker estimates and the two-worker minimum are preserved. | Source review of unchanged admission owners; Phase 3 admission remains separately required. |

The native helper fixture passing does not satisfy full compiler qualification.
