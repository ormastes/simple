# OCI retained request data codec

Source: `test/01_unit/lib/nogc_async_mut/container/providers/linux/oci_request_codec_spec.spl`.

Status: **AUTHORED / UNEXECUTED**. This source mirror is not runtime-generated
evidence. The admitted self-hosted runtime is unavailable.

The following 4 scenarios are authored acceptance checks. Expected results
come from their executable assertions, not from an observed run.

1. Roundtrips canonical data and stable digest without authorizing execution.
2. Rejects payload tampering unknown fields and noncanonical retained bytes.
3. Hashes vector boundaries and every new mode while separating operation identity.
4. Roundtrips execution fields; terminal argv construction is explicit while an
   unconfigured provider still refuses terminal effects.

Provider fixtures use real owner methods and exact argv matching. Optional real
journal persistence exercises canonical publication and format-preserving V1
cleanup; the executor-entry counter distinguishes attempted effects from matched
fixture consumption. The retained-request codec is data-only and does not grant
authority to use schema fields whose runtime effects remain refused.

No native container success, timing/RSS measurement, SPipe execution, docgen
PASS, or power-loss durability experiment is claimed. See
`doc/05_design/oci_request_binding_admission.md` for provenance, migration policy,
trusted-directory limits, and remaining verification.

The command follow-up admits the already-digested executable override. The
execution-options loop covers environment, working directory, and terminal
modes. Schema decoding still grants no execution authority by itself; mode
replay continues through the provider's actual immutable payload binding.

Execution-options source update (UNEXECUTED): Podman create vectors include
`--http-proxy=false`; typed environment/cwd are admitted. Managed Podman now
maps signed `stdin`/`tty` modes to explicit creation flags, while unconfigured
providers refuse them. See `doc/05_design/podman_primary_attach_v1.md` and its
authored, NOT_RUN primary attach scenarios. No live terminal claim is made.
