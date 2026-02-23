# Simple Test Runner Container Image
#
# Lightweight Alpine-based container for isolated test execution.
# Provides minimal runtime with Simple binary only.

FROM alpine:3.19

# Install runtime dependencies
RUN apk add --no-cache \
    bash \
    coreutils \
    findutils \
    ncurses-libs \
    libstdc++ \
    libgcc

# Create test user (non-root)
RUN addgroup -g 1000 testuser && \
    adduser -D -u 1000 -G testuser testuser

# Copy Simple runtime binary
COPY bin/release/simple /usr/local/bin/simple
RUN chmod +x /usr/local/bin/simple

# Create workspace
WORKDIR /workspace
RUN chown testuser:testuser /workspace

# Switch to non-root user for security
USER testuser

# Default command: run test suite
ENTRYPOINT ["/usr/local/bin/simple"]
CMD ["test"]

# Labels
LABEL org.opencontainers.image.title="Simple Test Runner"
LABEL org.opencontainers.image.description="Isolated test execution environment for Simple Language"
LABEL org.opencontainers.image.version="1.0.0"
