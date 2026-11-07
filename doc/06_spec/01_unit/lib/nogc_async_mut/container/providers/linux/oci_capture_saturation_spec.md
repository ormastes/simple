# Managed capture saturation

Source: `test/01_unit/lib/nogc_async_mut/container/providers/linux/oci_capture_saturation_spec.spl`.
Status: **AUTHORED_UNRUN**; two cases, no native or Podman qualification.

The common API wraps the actual Linux adapter and explicit scripted executor.
One case returns a native output-limit flag with CLI status zero and partial
logs: the API must reject the observation and retain workload identity. The
other combines the same flag with Podman's absent status one: it must produce
no absence receipt and must not sample a successful observation timestamp.

Managed ordinary capture uses `process_run_bounded_observed_v1` with the fixed
`OCI_MAX_OUTPUT_BYTES` limit (1 MiB per stream). The bound is supplied before
capture allocation. Structured timeout/output-limit metadata is rejected;
truncation markers and successful CLI status cannot establish complete output.
This API supplies no launch grant or fabricated deadline. Create/start continue
through the separately admitted capture route.

The native capture owner's allocation bounds, simultaneous stdout/stderr,
saturation, cleanup, and concurrency checks are separate prerequisites. The
scripted flag here tests consumer behavior only. It cannot qualify native
memory bounds, interpreter fallback, or live engine behavior.
