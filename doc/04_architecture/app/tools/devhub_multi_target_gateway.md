# DevHub multi-target gateway architecture

`config.spl` owns ordered SDN parsing, target selection, target projection, and non-destructive persistence. A selected `ItfConfig` is the request capsule: URL, deployment, gateway prefix, ordered headers, and target name move together. `auth.sdn` keys credentials by `confluence.<target>` with legacy fallback.

`request_headers.spl` validates transport-bound header text and applies explicit overrides. `auth.spl` resolves the API prefix. `cmd_api.spl` and `adapter_confluence.spl` consume the same selected capsule, so raw API and wiki traffic cannot drift. `redaction.spl` is the single diagnostic boundary. `atlassian_site.spl` owns hostname/deployment-shape comparison.

All invalid selector/header states fail before transport. Configured headers remain ordered to preserve duplicate values.

