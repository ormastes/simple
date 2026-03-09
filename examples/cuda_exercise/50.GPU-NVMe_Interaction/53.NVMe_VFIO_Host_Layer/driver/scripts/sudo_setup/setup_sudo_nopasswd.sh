#!/usr/bin/env bash
# setup_sudo_nopasswd.sh
# Configure passwordless sudo for Module 53 VFIO tests
#
# Usage:
#   ./setup_sudo_nopasswd.sh [build_dir]
#
# This script:
# 1. Creates helper scripts for VFIO bind/unbind
# 2. Configures sudoers.d for passwordless execution
# 3. Allows test executables to run without password

set -euo pipefail

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Detect build directory
if [[ $# -ge 1 ]]; then
    BUILD_DIR="$1"
else
    # Default to standard build directory
    SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
    REPO_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"
    BUILD_DIR="$REPO_ROOT/build"
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
RUNNER_SCRIPT="$SCRIPT_DIR/run_system_test.sh"
CTEST_PATH="$(command -v ctest 2>/dev/null || true)"

BUILD_DIR="$(realpath "$BUILD_DIR")"
CURRENT_USER="$USER"
SUDOERS_FILE="/etc/sudoers.d/99-nopasswd-vfio-${CURRENT_USER}"

echo -e "${GREEN}=== Module 53 VFIO Sudo Setup ===${NC}"
echo "User: $CURRENT_USER"
echo "Build directory: $BUILD_DIR"
echo "Sudoers file: $SUDOERS_FILE"
echo

# Check if running as root (we shouldn't be)
if [[ $EUID -eq 0 ]]; then
    echo -e "${RED}ERROR: Don't run this script as root. Run as your normal user.${NC}"
    echo "The script will use sudo internally when needed."
    exit 1
fi

# ============================================================================
# Step 1: Create VFIO helper scripts
# ============================================================================

echo -e "${YELLOW}[1/4] Creating VFIO helper scripts...${NC}"

# vfio-bind.sh
TMP_BIND=$(mktemp)
cat <<'BIND_EOF' > "$TMP_BIND"
#!/usr/bin/env bash
# vfio-bind.sh - Bind a PCI device to vfio-pci driver
set -euo pipefail

if [[ $# -ne 1 ]]; then
    echo "Usage: $(basename "$0") <BDF e.g. 0000:41:00.0>" >&2
    exit 2
fi

BDF="$1"

echo "[vfio-bind] Binding $BDF to vfio-pci..."

# Check if device exists
if [[ ! -d "/sys/bus/pci/devices/$BDF" ]]; then
    echo "ERROR: Device $BDF not found" >&2
    exit 1
fi

# Load vfio-pci module if not loaded
if ! lsmod | grep -q vfio_pci; then
    echo "[vfio-bind] Loading vfio-pci module..."
    modprobe vfio-pci
fi

# Unbind from current driver if bound
if [[ -e "/sys/bus/pci/devices/$BDF/driver" ]]; then
    CURRENT_DRIVER=$(basename "$(readlink "/sys/bus/pci/devices/$BDF/driver")")
    echo "[vfio-bind] Unbinding from current driver: $CURRENT_DRIVER"
    echo "$BDF" > "/sys/bus/pci/devices/$BDF/driver/unbind" || true
fi

# Set driver override and bind to vfio-pci
echo "[vfio-bind] Setting driver_override to vfio-pci..."
echo vfio-pci > "/sys/bus/pci/devices/$BDF/driver_override"

echo "[vfio-bind] Binding to vfio-pci..."
echo "$BDF" > /sys/bus/pci/drivers/vfio-pci/bind

echo "[vfio-bind] ✓ Successfully bound $BDF to vfio-pci"

# Show VFIO group
if [[ -e "/sys/bus/pci/devices/$BDF/iommu_group" ]]; then
    GROUP=$(basename "$(readlink "/sys/bus/pci/devices/$BDF/iommu_group")")
    echo "[vfio-bind] IOMMU group: $GROUP"
    echo "[vfio-bind] Device node: /dev/vfio/$GROUP"
fi
BIND_EOF
sudo cp "$TMP_BIND" /usr/local/sbin/vfio-bind.sh
rm -f "$TMP_BIND"

# vfio-unbind.sh
TMP_UNBIND=$(mktemp)
cat <<'UNBIND_EOF' > "$TMP_UNBIND"
#!/usr/bin/env bash
# vfio-unbind.sh - Unbind from vfio-pci and restore to native driver
set -euo pipefail

if [[ $# -ne 1 ]]; then
    echo "Usage: $(basename "$0") <BDF e.g. 0000:41:00.0>" >&2
    exit 2
fi

BDF="$1"

echo "[vfio-unbind] Unbinding $BDF from vfio-pci..."

# Check if device exists
if [[ ! -d "/sys/bus/pci/devices/$BDF" ]]; then
    echo "ERROR: Device $BDF not found" >&2
    exit 1
fi

# Unbind from vfio-pci if bound
if [[ -e /sys/bus/pci/drivers/vfio-pci/unbind ]]; then
    echo "[vfio-unbind] Unbinding from vfio-pci..."
    echo "$BDF" > /sys/bus/pci/drivers/vfio-pci/unbind 2>/dev/null || true
fi

# Clear driver override
echo "[vfio-unbind] Clearing driver_override..."
echo "" > "/sys/bus/pci/devices/$BDF/driver_override"

# Load nvme module if not loaded
if ! lsmod | grep -q "^nvme "; then
    echo "[vfio-unbind] Loading nvme module..."
    modprobe nvme
fi

# Bind to nvme driver
echo "[vfio-unbind] Binding to nvme driver..."
echo "$BDF" > /sys/bus/pci/drivers/nvme/bind || {
    echo "[vfio-unbind] WARNING: Failed to bind to nvme, device may need manual rebinding"
}

echo "[vfio-unbind] ✓ Successfully unbound $BDF from vfio-pci"
UNBIND_EOF
sudo cp "$TMP_UNBIND" /usr/local/sbin/vfio-unbind.sh
rm -f "$TMP_UNBIND"

# Make scripts executable
sudo chmod 0755 /usr/local/sbin/vfio-bind.sh /usr/local/sbin/vfio-unbind.sh

echo -e "${GREEN}✓ Created /usr/local/sbin/vfio-bind.sh${NC}"
echo -e "${GREEN}✓ Created /usr/local/sbin/vfio-unbind.sh${NC}"

# ============================================================================
# Step 2: Find test executables in build directory
# ============================================================================

echo
echo -e "${YELLOW}[2/4] Locating test executables...${NC}"

TEST_EXECUTABLES=()

# Module 53 test executables
M53_TESTS=(
    "test_host_io_system"
    "test_setup_tasks"
    "setup_helper_example"
)

for test_name in "${M53_TESTS[@]}"; do
    # Try multiple possible locations
    possible_paths=(
        "$BUILD_DIR/50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/test/system_test/$test_name"
        "$BUILD_DIR/50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/test/helper/$test_name"
    )

    for test_path in "${possible_paths[@]}"; do
        if [[ -f "$test_path" && -x "$test_path" ]]; then
            TEST_EXECUTABLES+=("$test_path")
            echo -e "${GREEN}  Found: $test_path${NC}"
            break
        fi
    done
done

if [[ ${#TEST_EXECUTABLES[@]} -eq 0 ]]; then
    echo -e "${YELLOW}  WARNING: No test executables found in build directory${NC}"
    echo "  Make sure you've built the project first"
    echo "  Tests will be added to sudoers but may not work until built"
fi

# ============================================================================
# Step 3: Create sudoers configuration
# ============================================================================

echo
echo -e "${YELLOW}[3/4] Creating sudoers configuration...${NC}"

# Build sudoers content
SUDOERS_CONTENT="# Passwordless sudo for Module 53 VFIO tests
# Generated by setup_sudo_nopasswd.sh
# User: $CURRENT_USER

# VFIO helper scripts
$CURRENT_USER ALL=(root) NOPASSWD: /usr/local/sbin/vfio-bind.sh
$CURRENT_USER ALL=(root) NOPASSWD: /usr/local/sbin/vfio-unbind.sh

# Kernel module management
$CURRENT_USER ALL=(root) NOPASSWD: /usr/sbin/modprobe vfio-pci
$CURRENT_USER ALL=(root) NOPASSWD: /usr/sbin/modprobe nvme
$CURRENT_USER ALL=(root) NOPASSWD: /usr/sbin/rmmod vfio-pci
$CURRENT_USER ALL=(root) NOPASSWD: /usr/sbin/rmmod nvme

# Test executables (specific paths)
"

# Add each test executable
for test_exe in "${TEST_EXECUTABLES[@]}"; do
    SUDOERS_CONTENT+="$CURRENT_USER ALL=(root) NOPASSWD: $test_exe
"
done

# Add wildcard for any test executable in the build directory
# This handles rebuilt tests and new test executables
SUDOERS_CONTENT+="
# Allow any test executable in Module 53 build directories
$CURRENT_USER ALL=(root) NOPASSWD: $BUILD_DIR/50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/test/*/*
$CURRENT_USER ALL=(root) NOPASSWD: $BUILD_DIR/50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/test/*/test_*
"

# Allow convenience runner script if present
if [[ -x "$RUNNER_SCRIPT" ]]; then
    SUDOERS_CONTENT+="
# Module 53 aggregated system test runner
$CURRENT_USER ALL=(root) NOPASSWD: $RUNNER_SCRIPT
"
fi

# Allow ctest so suites can be launched without extra prompts
if [[ -n "$CTEST_PATH" ]]; then
    SUDOERS_CONTENT+="
# Permit ctest to launch Module 53 tests under sudo
$CURRENT_USER ALL=(root) NOPASSWD: $CTEST_PATH
"
fi

# Write to temporary file first, then validate with visudo
TMP_SUDOERS=$(mktemp)
echo "$SUDOERS_CONTENT" > "$TMP_SUDOERS"

# Validate syntax
if ! sudo visudo -c -f "$TMP_SUDOERS" >/dev/null 2>&1; then
    echo -e "${RED}ERROR: Generated sudoers file has syntax errors${NC}"
    sudo visudo -c -f "$TMP_SUDOERS"
    rm -f "$TMP_SUDOERS"
    exit 1
fi

# Install the sudoers file
sudo cp "$TMP_SUDOERS" "$SUDOERS_FILE"
sudo chmod 0440 "$SUDOERS_FILE"
sudo chown root:root "$SUDOERS_FILE"
rm -f "$TMP_SUDOERS"

echo -e "${GREEN}✓ Created $SUDOERS_FILE${NC}"

# ============================================================================
# Step 4: Test configuration
# ============================================================================

echo
echo -e "${YELLOW}[4/4] Testing configuration...${NC}"

# Test vfio-bind.sh access
if sudo -n /usr/local/sbin/vfio-bind.sh 2>&1 | grep -q "Usage:"; then
    echo -e "${GREEN}✓ vfio-bind.sh: No password required${NC}"
else
    echo -e "${RED}✗ vfio-bind.sh: Still requires password${NC}"
fi

# Test vfio-unbind.sh access
if sudo -n /usr/local/sbin/vfio-unbind.sh 2>&1 | grep -q "Usage:"; then
    echo -e "${GREEN}✓ vfio-unbind.sh: No password required${NC}"
else
    echo -e "${RED}✗ vfio-unbind.sh: Still requires password${NC}"
fi

# Test modprobe access
if sudo -n /usr/sbin/modprobe --help >/dev/null 2>&1; then
    echo -e "${GREEN}✓ modprobe: No password required${NC}"
else
    echo -e "${RED}✗ modprobe: Still requires password${NC}"
fi

# ============================================================================
# Summary
# ============================================================================

echo
echo -e "${GREEN}=== Setup Complete ===${NC}"
echo
echo "You can now run the following commands without a password:"
echo
echo "  1. Bind NVMe device to vfio-pci:"
echo -e "     ${YELLOW}sudo /usr/local/sbin/vfio-bind.sh 0000:41:00.0${NC}"
echo
echo "  2. Unbind from vfio-pci (restore to nvme):"
echo -e "     ${YELLOW}sudo /usr/local/sbin/vfio-unbind.sh 0000:41:00.0${NC}"
echo
echo "  3. Run Module 53 tests:"
for test_exe in "${TEST_EXECUTABLES[@]}"; do
    echo -e "     ${YELLOW}sudo -E $test_exe${NC}"
done
echo
step_index=4
if [[ -x "$RUNNER_SCRIPT" ]]; then
    echo "  ${step_index}. Run aggregated system-test helper:"
    echo -e "     ${YELLOW}sudo -E $RUNNER_SCRIPT${NC}"
    echo
    step_index=$((step_index + 1))
fi
if [[ -n "$CTEST_PATH" ]]; then
    echo "  ${step_index}. Launch ctest suites:"
    echo -e "     ${YELLOW}sudo -E ctest -R \"HostIo.*\"${NC}"
    echo
    step_index=$((step_index + 1))
fi
echo "  ${step_index}. Load/unload kernel modules:"
echo -e "     ${YELLOW}sudo modprobe vfio-pci${NC}"
echo -e "     ${YELLOW}sudo rmmod vfio-pci${NC}"
echo
echo "Note: Use 'lspci -nn | grep -i nvme' to find your NVMe BDF address"
echo
echo -e "${YELLOW}Configuration file: $SUDOERS_FILE${NC}"
echo "To remove: sudo rm $SUDOERS_FILE"
echo
