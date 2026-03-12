FROM ubuntu:24.04

ARG DEBIAN_FRONTEND=noninteractive

RUN apt-get update && \
    apt-get install -y --no-install-recommends \
        fontconfig \
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
        libxpm4 \
        libxrender1 \
        libxt6t64 \
        netcat-openbsd \
        procps \
        usbutils \
        x11-utils \
        xauth \
        xfonts-75dpi \
        xfonts-base \
        xvfb && \
    rm -rf /var/lib/apt/lists/*

# Legacy libs removed from Ubuntu 24.04, manually bundled for 2013-era t32marm
COPY libXp.so.6 /lib/x86_64-linux-gnu/libXp.so.6
COPY libjpeg.so.62.0.0 /lib/x86_64-linux-gnu/libjpeg.so.62.0.0
RUN ln -sf libjpeg.so.62.0.0 /lib/x86_64-linux-gnu/libjpeg.so.62 && ldconfig

# Qt4 compat libs for t32marm-qt fallback (2013-era binary needs Qt 4)
# Ubuntu 24.04 no longer packages Qt4; install only if available
RUN apt-get update && \
    apt-get install -y --no-install-recommends \
        libqtcore4 libqtgui4 2>/dev/null || true && \
    rm -rf /var/lib/apt/lists/*

# Remove bitmap font blocker and rebuild font cache
# Create XtErrorDB symlink — 2013-era t32marm expects this file but
# modern libxt merged it into XErrorDB
RUN rm -f /etc/fonts/conf.d/70-no-bitmaps-except-emoji.conf && \
    fc-cache -f && \
    ln -sf /usr/share/X11/XErrorDB /usr/share/X11/XtErrorDB

WORKDIR /workspace

ENV T32_CONFIG=/workspace/config/t32/t32_stm_headless.t32
ENV HOME=/tmp
ENV XAPPLRESDIR=/opt/t32

COPY trace32_entrypoint.shs /usr/local/bin/trace32_entrypoint.shs
RUN chmod +x /usr/local/bin/trace32_entrypoint.shs

CMD ["/usr/local/bin/trace32_entrypoint.shs"]
