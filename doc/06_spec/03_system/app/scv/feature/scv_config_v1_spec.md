# Native SCV configuration component scenarios

Status: authored manual outline; **not_run**. This is not generated execution evidence. Executable source: `test/03_system/app/scv/feature/scv_config_v1_spec.spl`. Regenerate and review using the admitted SPipe/docgen runtime before claiming a qualified manual.

The scenarios use the approved setup/capture/exercise/evidence/assert vocabulary and call the actual descriptor-relative loader, strict SDN parser, configuration schema, route matcher and authority intersection. They do not call a mock parser or manufacture acceptance receipts.

1. Create a private repository containing the exact native nested config and named route table. Load it, route a data `.sdn` object to `database_data`/`sdn_rows`, bind both raw input hashes and confirm bytes remain unchanged.
2. Request required native configuration from an empty repository. Refuse, and show that only explicit legacy selection returns an unvalidated profile.
3. Replace the intermediate `config` directory with a symlink to another owned directory containing valid files. Refuse before reading config through the link.
4. Retain a valid parsed generation, preserve a proposed typo as private bytes, and refuse the new load. Confirm the prior value still routes and the invalid submitted bytes remain present.
5. Parse proposed routes that weaken a policy role. Judge a protected rename using only the old supplied routes, refuse the transition and preserve its old role.
6. Supply local/CLI capability requests alongside separate host and old accepted constraints. Confirm denied network/executable/LLM capabilities stay denied, unapproved providers disappear, and the smallest memory ceiling wins.

Missing integration evidence: actual CLI/provider caller, provider-lock/artifact admission, immutable accepted generations, independent old-policy authorization receipts, cross-host support and startup/latency/RSS measurements. Component source coverage is not a full SCV acceptance claim.
