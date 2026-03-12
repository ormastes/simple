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
        libxcursor1 \
        libxext6 \
        libxfixes3 \
        libxft2 \
        libxmu6 \
        libxp6 \
        libxpm4 \
        libxrender1 \
        libxt6 \
        procps \
        usbutils \
        x11-utils \
        xauth \
        xfonts-75dpi \
        xfonts-base \
        xvfb && \
    rm -rf /var/lib/apt/lists/*

# Qt4 compat libs for t32marm-qt fallback (2013-era binary needs Qt 4)
# Ubuntu 24.04 no longer packages Qt4; install only if available
RUN apt-get update && \
    apt-get install -y --no-install-recommends \
        libqtcore4 libqtgui4 2>/dev/null || true && \
    rm -rf /var/lib/apt/lists/*

# Remove bitmap font blocker and rebuild font cache
RUN rm -f /etc/fonts/conf.d/70-no-bitmaps-except-emoji.conf && \
    fc-cache -f

WORKDIR /workspace

ENV T32_CONFIG=/workspace/config/t32/t32_stm_headless.t32
ENV HOME=/tmp
ENV XAPPLRESDIR=/opt/t32

COPY config/t32/trace32_entrypoint.shs /usr/local/bin/trace32_entrypoint.shs
RUN chmod +x /usr/local/bin/trace32_entrypoint.shs

CMD ["/usr/local/bin/trace32_entrypoint.shs"]
