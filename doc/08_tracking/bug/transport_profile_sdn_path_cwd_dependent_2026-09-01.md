# Transport-profile checks fail silently-plausibly when run from any cwd but the repo root

**Date:** 2026-09-01
**Found by:** parent session, while (incorrectly) investigating a suspected regression.
**Status:** OPEN — latent, and it already produced one false regression report.

## Measured

`examples/09_embedded/simpleos_nvme_fw/fw/nvme_transport_config.spl:18`

```simple
val PROFILE_SDN: text = "examples/09_embedded/simpleos_nvme_fw/fw/nvme_transport_profiles.sdn"
```

A **relative** path, resolved against the process cwd. `file_read_text` at `:96`
returns nothing when the cwd is not the repo root, and the loader — correctly
fail-closed — returns `valid == 0`.

Same binary, same tree, same files; only the cwd differs:

| cwd | admin_transport | nvme_registers | host_equiv |
|---|---|---|---|
| repo root | 112 PASS / 0 FAIL `OK` | 138 / 0 `OK` | 86 PASS `OK` |
| `.../fw` | 57 / 55 `FAIL (55)` | 90 / 48 `FAIL (48)` | 48 / 42 `FAIL (38)` |

## Why it matters more than a path bug

The failure mode is **plausible**, not obvious. It presents as dozens of
substantive assertion failures (`CAP.MQES is 0-based: depth 64 reports 63 --
expected 63 got 0`) rather than as "config not found". Every one of those is a
downstream consequence of an all-zero profile, but each reads like a real defect
in the register/transport logic.

This session it caused a false accusation: the parent had verified these three
checks green, re-ran them from `fw/`, saw them red, and wrongly contradicted the
agent that reported them as unaffected. The agent's attribution was right.

Fail-closed was the correct design and did its job — the loader refused to invent
a profile. The defect is that the *reason* is invisible at the point of failure.

## Required

1. Resolve the path relative to the module/source location, or search upward for
   a repo marker, so the checks are cwd-independent.
2. Failing that (or in addition): when `file_read_text` yields nothing, print one
   explicit diagnostic naming the attempted absolute path, so a zeroed profile
   can never again masquerade as 48 logic failures.
3. Consider a single early assertion in each affected `*_check.spl` — "profile
   loaded" — so the first FAIL line states the real cause instead of the
   fiftieth symptom.

## Caveat

Measured on the Rust bootstrap seed; the behaviour is a path-resolution property
and is not seed-specific.
