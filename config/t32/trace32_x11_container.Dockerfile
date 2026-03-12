FROM ubuntu:24.04

ARG DEBIAN_FRONTEND=noninteractive

RUN apt-get update && \
    apt-get install -y --no-install-recommends \
        libfontconfig1 \
        libfreetype6 \
        libice6 \
        libjpeg-turbo8 \
        libsm6 \
        libx11-6 \
        libxext6 \
        libxft2 \
        libxmu6 \
        libxp6 \
        libxpm4 \
        libxt6 \
        procps \
        usbutils \
        x11-utils \
        xauth \
        xvfb && \
    rm -rf /var/lib/apt/lists/*

WORKDIR /workspace

ENV T32_CONFIG=/workspace/config/t32/t32_stm_headless.t32

CMD ["sh", "-lc", "xvfb-run -a /opt/t32/bin/pc_linux64/t32marm -c \"$T32_CONFIG\""]
