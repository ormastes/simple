# Fresh configured execution-user observation

The typed command selects `podman container inspect`, so another object kind
cannot be selected by generic inspect fallback. Podman's
[container inspect documentation](https://docs.podman.io/en/latest/markdown/podman-container-inspect.1.html)
defines this container-only command. The official v5.2.5 command source
(`cmd/podman/containers/inspect.go`, blob `85d4cd8886c1d33fc0ed49d8d46363e493db506b`)
forces the container type and documents the `.Id` template spelling used here.

Status: AUTHORED / UNEXECUTED. No native runtime, build or conformance result is claimed.

The managed Linux Podman provider reads an exact full64 retained V2 native identity with a fresh typed `inspect --format FORMAT ID`. The format emits one JSON object containing the native ID, all five original request identity labels and `Config.User`, each escaped by the engine's JSON template function. The absolute approved engine route and fresh policy-baseline guard are the existing executor owner; no independent process or PATH fallback is added.

The parser bounds output to 16 KiB and preflights string/escape-aware flat object structure before the strict duplicate/trailing JSON parser. It requires exactly seven string fields, exact retained identity, and a nonempty user of at most 128 bytes without ASCII controls. Nested objects/arrays, malformed/unknown fields and saturated capture cannot qualify. Braces, quotes and escapes inside strings remain data. Empty image/default user is explicitly unresolved.

This observes configured user metadata. Numeric text is not proof of a running process UID; a named user is not a resolved UID, and rootless host UID is not container execution-user evidence. The observation operation carries actual routed argv, stdout/stderr, CLI exit status and an UNKNOWN lifecycle phase with state exit code -1. It changes no journal or lifecycle state.

The adapter validates the canonical common request/scope, applies its operation duration bound, invokes the leaf observation and hashes the actual query/observation into `ContainerExecutionUserReceiptV2`. The common facade is `simple_container_execution_user_v2`; receipt proof kind is `exact-native-execution-user-v1`. Canonical shape/digest is data integrity rather than producer authentication. Remote enrollment must separately authorize its producer and same-process identity evidence.

Six focused authored unit scenarios exercise the actual parser, builder and common dispatch over explicit managed scripted providers: exact independent argv; numeric/name parsing; malformed JSON/input controls; positive common receipts; request/scope/identity pre-query rejection; empty/saturated/error/mismatch/policy refusal. All are UNEXECUTED. Common receipt/facade integration is a separate prerequisite owned by orchestration.
