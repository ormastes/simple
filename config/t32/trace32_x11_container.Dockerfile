FROM ubuntu:24.04

ARG DEBIAN_FRONTEND=noninteractive

RUN apt-get update && \
    apt-get install -y --no-install-recommends \
        fontconfig \
        libice6 \
        libjpeg62 \
        libsm6 \
        libx11-6 \
        libxext6 \
        libxft2 \
        libxmu6 \
        libxpm4 \
        libxt6 \
        netcat-openbsd \
        procps \
        usbutils \
        xauth \
        x11-utils && \
    rm -rf /var/lib/apt/lists/*

WORKDIR /workspace

ENV T32_CONFIG=/workspace/config/t32/t32_stm_headless.t32
ENV HOME=/tmp
ENV XAPPLRESDIR=/opt/t32

COPY trace32_entrypoint.shs /usr/local/bin/trace32_entrypoint.shs
RUN chmod +x /usr/local/bin/trace32_entrypoint.shs

CMD ["/usr/local/bin/trace32_entrypoint.shs"]
