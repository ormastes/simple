# SCV native configuration component verification plan

Status: not_run, 2026-10-27. Parent runtime owner must supply an admitted pure-Simple binary; no seed or bootstrap fallback.

| Requirement | Actual owner/oracle | Planned evidence |
|---|---|---|
| SCVN-C01 / AT-C01 subset | Strict bytes parser → exact eight-section schema → named route table | Exact master §5.3/5.4 fixture values, raw SHA-256, real file loader |
| SCVN-C01 / AT-C02 subset | Reject duplicates, malformed input, unknown keys, types, units, unsafe values and invalid version | Specific diagnostic checks, byte/depth/node bounds and invalid UTF-8 |
| SCVN-C01 / containment | Shared descriptor-relative beneath-open with actual size bound | Final/intermediate symlink rejection, traversal/nonregular/empty/limit cases and descriptor pool exhaustion control |
| SCVN-C02 / AT-C03 subset | Accepted route owner, bounded component globs | Identical SDN extensions select config/schema/data; recursive zero-depth case; overlaps reject regardless order |
| SCVN-C02/C03 / AT-C04 subset | Explicit old accepted routes and policy intersection | Protected rename refused even when weaker candidate routes parse; local/CLI grants denied, smallest budget enforced |
| SCVN-C03 / identity | Framed canonical effective configuration | Raw formatting changes raw SHA only; route/profile/policy/limit changes effective digest |

Execute `test/01_unit/lib/common/io/read_only_file_view_bounded_beneath_v1_spec.spl`, `test/01_unit/lib/scv/scv_config_v1_spec.spl` and `test/03_system/app/scv/feature/scv_config_v1_spec.spl` once with the admitted runtime. Capture actual command, executable provenance/hash, source head, exit status, scenario/assertion counts and failures. Generate/review the system manual and run SSpec maintenance only after admission. Do not infer full AT-C01/C04/C05 PASS from these component cases: provider manifests/locks, accepted-policy admission, CLI wiring and exact artifact derivation identities remain parent-owned integration gates.
