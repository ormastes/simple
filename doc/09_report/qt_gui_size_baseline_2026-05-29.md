# Qt GUI Size Baseline

Date: 2026-05-29

## Status

- qt_build=unavailable
- reason=missing_qt_tooling
- qt_pkg=unavailable
- simple_web_report=doc/09_report/web_baremetal_size_audit_2026-05-28.md
- status=optional_baseline_unavailable
- verification_effect=non_blocking
- requirement=REQ-011 / NFR-005

## Qt Artifact

| Artifact | Bytes | ELF dec |
|---|---:|---:|
| qt_minimal_gui | n/a | n/a |

Interpretation: Qt development files were not available through pkg-config, so no Qt artifact size can be measured on this host.

## Loaded Libraries

- unavailable

## Notes

- This script does not install Qt or network dependencies.
- Missing Qt records an unavailable baseline instead of failing the Simple verification path.
- Use `scripts/check-web-baremetal-size-audit.shs` for the Simple web-render artifact side of the comparison.
- A release or CI gate may require this baseline only when the environment explicitly provisions Qt and sets that expectation outside this script.
