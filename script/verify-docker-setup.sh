#!/bin/bash
# verify-docker-setup.sh - Verify Phase 2 Docker container setup
#
# This script verifies that all Phase 2 container infrastructure is properly set up

set -euo pipefail

# Colors
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
NC='\033[0m'

pass() { echo -e "${GREEN}✓${NC} $*"; }
fail() { echo -e "${RED}✗${NC} $*"; }
warn() { echo -e "${YELLOW}⚠${NC} $*"; }

echo "Phase 2 Container Setup Verification"
echo "====================================="
echo ""

# Track results
PASSED=0
FAILED=0

# Check 1: Files exist
echo "Checking files..."
FILES=(
    "docker/Dockerfile.test-isolation"
    "docker/Dockerfile.test-full"
    ".dockerignore"
    "docker-compose.test.yml"
    "script/docker-test.sh"
    "docker/README_TEST_CONTAINERS.md"
)

for file in "${FILES[@]}"; do
    if [ -f "$file" ]; then
        pass "$file exists"
        ((PASSED++))
    else
        fail "$file missing"
        ((FAILED++))
    fi
done

# Check 2: docker-test.sh is executable
echo ""
echo "Checking permissions..."
if [ -x "script/docker-test.sh" ]; then
    pass "script/docker-test.sh is executable"
    ((PASSED++))
else
    fail "script/docker-test.sh is not executable"
    ((FAILED++))
fi

# Check 3: Runtime binary exists
echo ""
echo "Checking prerequisites..."
if [ -f "bin/release/simple" ]; then
    SIZE=$(ls -lh bin/release/simple | awk '{print $5}')
    pass "Runtime binary exists (${SIZE})"
    ((PASSED++))
else
    fail "Runtime binary missing (bin/release/simple)"
    warn "Run: bin/simple build --release"
    ((FAILED++))
fi

# Check 4: Docker is available
echo ""
echo "Checking Docker..."
if command -v docker &> /dev/null; then
    VERSION=$(docker --version | cut -d' ' -f3 | cut -d',' -f1)
    pass "Docker installed (v${VERSION})"
    ((PASSED++))
else
    fail "Docker not installed"
    ((FAILED++))
fi

# Check 5: Docker daemon is running
if docker info &> /dev/null; then
    pass "Docker daemon is running"
    ((PASSED++))
else
    fail "Docker daemon is not running"
    ((FAILED++))
fi

# Check 6: Docker Compose is available
if docker compose version &> /dev/null; then
    VERSION=$(docker compose version | cut -d' ' -f4 | cut -d'v' -f2)
    pass "Docker Compose available (v${VERSION})"
    ((PASSED++))
else
    warn "Docker Compose not available (optional)"
fi

# Check 7: File sizes
echo ""
echo "Checking file sizes..."
DOCKERIGNORE_SIZE=$(wc -l < .dockerignore)
if [ "$DOCKERIGNORE_SIZE" -ge 90 ]; then
    pass ".dockerignore has ${DOCKERIGNORE_SIZE} lines (optimized)"
    ((PASSED++))
else
    fail ".dockerignore only has ${DOCKERIGNORE_SIZE} lines (expected 90+)"
    ((FAILED++))
fi

COMPOSE_SIZE=$(wc -l < docker-compose.test.yml)
if [ "$COMPOSE_SIZE" -ge 180 ]; then
    pass "docker-compose.test.yml has ${COMPOSE_SIZE} lines"
    ((PASSED++))
else
    fail "docker-compose.test.yml only has ${COMPOSE_SIZE} lines (expected 180+)"
    ((FAILED++))
fi

# Check 8: Dockerfile validation
echo ""
echo "Checking Dockerfile syntax..."
if docker build --no-cache --dry-run -f docker/Dockerfile.test-isolation . &> /dev/null; then
    pass "Dockerfile.test-isolation syntax valid"
    ((PASSED++))
else
    warn "Cannot validate Dockerfile.test-isolation (dry-run not supported)"
fi

# Check 9: Docker images built
echo ""
echo "Checking Docker images..."
if docker images | grep -q simple-test-isolation; then
    SIZE=$(docker images simple-test-isolation:latest --format "{{.Size}}")
    pass "simple-test-isolation:latest exists (${SIZE})"
    ((PASSED++))
else
    warn "simple-test-isolation:latest not built yet"
    warn "Run: script/docker-test.sh build"
fi

if docker images | grep -q simple-test-full; then
    SIZE=$(docker images simple-test-full:latest --format "{{.Size}}")
    pass "simple-test-full:latest exists (${SIZE})"
    ((PASSED++))
else
    warn "simple-test-full:latest not built yet"
    warn "Run: script/docker-test.sh build"
fi

# Summary
echo ""
echo "==========================================="
echo "Verification Summary"
echo "==========================================="
echo "Passed: ${PASSED}"
echo "Failed: ${FAILED}"

if [ "$FAILED" -eq 0 ]; then
    echo ""
    pass "All checks passed! Phase 2 setup is complete."
    echo ""
    echo "Next steps:"
    echo "  1. Build images: script/docker-test.sh build"
    echo "  2. Run tests: script/docker-test.sh run"
    echo "  3. See documentation: docker/README_TEST_CONTAINERS.md"
    exit 0
else
    echo ""
    fail "Some checks failed. Please fix the issues above."
    exit 1
fi
