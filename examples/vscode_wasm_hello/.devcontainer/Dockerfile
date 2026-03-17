FROM mcr.microsoft.com/devcontainers/typescript-node:20

# WASM tools + GUI debugging (noVNC) + headless VSCode test deps
RUN apt-get update && apt-get install -y --no-install-recommends \
    wabt \
    xvfb \
    x11vnc \
    fluxbox \
    novnc \
    websockify \
    libxkbfile-dev \
    pkg-config \
    libsecret-1-dev \
    libxss1 \
    libasound2 \
    libgtk-3-0 \
    libnss3 \
    libgbm1 \
    && rm -rf /var/lib/apt/lists/*

ENV DISPLAY=:99
