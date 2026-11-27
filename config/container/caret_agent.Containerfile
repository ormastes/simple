# Image for a caret-suite agent launched by cs with `--container`.
#
# Contents: a glibc userland new enough for the Simple binary (the binary
# needs GLIBC_2.39; trixie ships 2.41), libgcc_s (the binary's only other
# shared dependency), git for the agent's commits, and the small tools an
# agent's shell commands reach for. No compiler: the Simple binary and the
# repository are bind-mounted from the host at run time, never baked in.
#
# Build (rootless, no GCC involved):
#   podman build -t localhost/simple-caret-agent:1 -f config/container/caret_agent.Containerfile config/container
FROM docker.io/library/debian:trixie-slim
RUN apt-get update \
 && apt-get install -y --no-install-recommends git ca-certificates libgcc-s1 procps \
 && rm -rf /var/lib/apt/lists/*
# The agent runs as the invoking host user (`--userns keep-id`), who has no
# passwd entry or home in the image; cs sets HOME=/tmp.
ENV LANG=C.UTF-8
