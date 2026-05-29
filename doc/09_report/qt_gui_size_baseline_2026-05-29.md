# Qt GUI Size Baseline

Date: 2026-05-29

## Status

- qt_build=unavailable
- reason=missing_qt_tooling
- qt_pkg=unavailable
- simple_web_report=doc/09_report/web_baremetal_size_audit_2026-05-28.md
- simple_artifact=Simple web placeholder URL facade
- simple_bytes=14336
- comparison_status=unavailable
- comparison_reason=qt_baseline_unavailable

## Qt Artifact

| Artifact | Bytes | ELF dec |
|---|---:|---:|
| qt_minimal_gui | n/a | n/a |

## Simple Web Artifact

| Artifact | Bytes | ELF dec |
|---|---:|---:|
| Simple web placeholder URL facade | 14336 | 3889 |

## Loaded Libraries

- unavailable

## Notes

- This script does not install Qt or network dependencies.
- Missing Qt records an unavailable baseline instead of failing the Simple verification path.
- The comparison passes only when a Qt artifact and a Simple Web artifact are both measured.
- Use `scripts/check-web-baremetal-size-audit.shs` to refresh the Simple web-render artifact side of the comparison.
