# Simple Language - UI Debug Container
#
# Combines toolchain from Dockerfile.test-isolation + GUI deps from Dockerfile.vscode-test
# Provides Rust dev environment + Xvfb/noVNC for UI debugging.
#
# Build:  docker build -t simple-debug -f .devcontainer/Dockerfile .devcontainer/
# Use:    VSCode "Reopen in Container" or "Dev Containers: Open Folder in Container"

FROM mcr.microsoft.com/devcontainers/rust:1

ENV DEBIAN_FRONTEND=noninteractive

# Compiler toolchain (from Dockerfile.test-isolation)
# + GUI/Electron deps (from Dockerfile.vscode-test)
# + VNC stack (from vscode_wasm_hello)
# + debug tools
RUN apt-get update && apt-get install -y --no-install-recommends \
    clang lld llvm gcc libc6-dev binutils make \
    xvfb x11vnc fluxbox novnc websockify \
    libgtk-3-0 libgbm1 libnss3 libxss1 libasound2t64 \
    libx11-xcb1 libxcb-dri3-0 libdrm2 libatk1.0-0 \
    libatk-bridge2.0-0 libatspi2.0-0 libcups2 \
    libxcomposite1 libxdamage1 libxrandr2 libpango-1.0-0 \
    fonts-liberation xdg-utils gdb strace \
    && rm -rf /var/lib/apt/lists/*

# Node.js 20 LTS (for web UI mode)
RUN curl -fsSL https://deb.nodesource.com/setup_20.x | bash - \
    && apt-get install -y nodejs && rm -rf /var/lib/apt/lists/*

ENV DISPLAY=:99
WORKDIR /workspace
