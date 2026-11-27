# Linux engine-declared workspace Mounts manual

Status: **AUTHORED_NOT_RUN**. No query was executed against Podman.

The mirrored executable spec checks exact source/destination/read-only/type,
spaces in source names, full container ID and generation labels, rejected extra
binds and shadow aliases, malformed/duplicate JSON, bounded input/depth, and
receipt query/identity correlation for the configured provider path.

The production module constructs a trusted constant inspect template. Authored
paths and shell fragments never enter the template or command language. It
consumes a retained provider `RuntimeOperationV1` receipt and checks the exact
configured query plus expected identity before parsing its stdout.

Podman describes [container inspect](https://docs.podman.io/en/latest/markdown/podman-container-inspect.1.html)
as configuration output. This parser checks its **engine-declared mount
projection**, not exhaustive runtime/kernel mounts. It does not prove target
mount namespace, guest exclusion of the Host parent or engine endpoint, native
source-object identity, permission enforcement or launch authority. Copied
operation records are still data; the consumer must obtain its receipt from
the actual retained provider. The generic Linux mount effect refusal remains.

A future native fixture must exercise the constant template and actual provider
receipt path, distinguish configuration from kernel namespace evidence, and
prove parent mutation control across create/inspect before launch support is
qualified. No disabled or unsupported fixture is a passing engine result.
