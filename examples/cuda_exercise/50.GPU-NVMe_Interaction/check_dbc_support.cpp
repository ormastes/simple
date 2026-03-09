/**
 * @file check_dbc_support.cpp
 * @brief Utility to check actual DBC support on NVMe devices
 */

#include <iostream>
#include <fcntl.h>
#include <unistd.h>
#include <sys/ioctl.h>
#include <linux/nvme_ioctl.h>
#include <cstring>
#include <cstdio>
#include <cstdint>

// Structure for NVMe Identify Controller data
struct nvme_id_ctrl {
    uint8_t data[4096];
};

bool check_dbc_support(const char* device_path) {
    int fd = open(device_path, O_RDONLY);
    if (fd < 0) {
        std::cerr << "Failed to open " << device_path << ": " << strerror(errno) << std::endl;
        return false;
    }

    // Prepare identify command
    nvme_id_ctrl id_ctrl;
    memset(&id_ctrl, 0, sizeof(id_ctrl));

    struct nvme_admin_cmd cmd = {};
    cmd.opcode = 0x06;  // NVME_ADMIN_IDENTIFY
    cmd.nsid = 0;
    cmd.addr = (uint64_t)&id_ctrl;
    cmd.data_len = sizeof(id_ctrl);
    cmd.cdw10 = 1;  // Controller identify

    // Send identify command
    if (ioctl(fd, NVME_IOCTL_ADMIN_CMD, &cmd) < 0) {
        std::cerr << "NVME_IOCTL_ADMIN_CMD failed: " << strerror(errno) << std::endl;
        close(fd);
        return false;
    }

    // Extract OACS (Optional Admin Command Support) at byte offset 256
    uint16_t oacs = *(uint16_t*)&id_ctrl.data[256];

    // Extract version at byte 8
    uint32_t vs = *(uint32_t*)&id_ctrl.data[8];
    uint8_t major = (vs >> 16) & 0xFF;
    uint8_t minor = (vs >> 8) & 0xFF;

    // Extract model name (bytes 24-63)
    char model[41] = {0};
    memcpy(model, &id_ctrl.data[24], 40);
    // Trim trailing spaces
    for (int i = 39; i >= 0; i--) {
        if (model[i] == ' ' || model[i] == '\0') {
            model[i] = '\0';
        } else {
            break;
        }
    }

    // Check bit 8 for DBC support
    bool dbc_supported = (oacs & (1 << 8)) != 0;

    std::cout << "\n========================================" << std::endl;
    std::cout << "Device: " << device_path << std::endl;
    std::cout << "Model: " << model << std::endl;
    std::cout << "NVMe Version: " << (int)major << "." << (int)minor << std::endl;
    std::cout << "OACS Value: 0x" << std::hex << oacs << std::dec << std::endl;
    std::cout << "OACS Binary: ";
    for (int i = 15; i >= 0; i--) {
        std::cout << ((oacs & (1 << i)) ? "1" : "0");
        if (i == 8) std::cout << " "; // Highlight bit 8
    }
    std::cout << std::endl;
    std::cout << "Bit 8 (DBC): " << (dbc_supported ? "SET (DBC Supported)" : "NOT SET (No DBC)") << std::endl;

    // Check other interesting OACS bits
    std::cout << "\nOther OACS Features:" << std::endl;
    if (oacs & (1 << 0)) std::cout << "  Bit 0: Security Send/Receive" << std::endl;
    if (oacs & (1 << 1)) std::cout << "  Bit 1: Format NVM" << std::endl;
    if (oacs & (1 << 2)) std::cout << "  Bit 2: Firmware Download/Commit" << std::endl;
    if (oacs & (1 << 3)) std::cout << "  Bit 3: Namespace Management" << std::endl;
    if (oacs & (1 << 4)) std::cout << "  Bit 4: Device Self-test" << std::endl;
    if (oacs & (1 << 5)) std::cout << "  Bit 5: Directives" << std::endl;
    if (oacs & (1 << 6)) std::cout << "  Bit 6: NVMe-MI Send/Receive" << std::endl;
    if (oacs & (1 << 7)) std::cout << "  Bit 7: Virtualization Management" << std::endl;
    if (oacs & (1 << 8)) std::cout << "  Bit 8: Doorbell Buffer Config (DBC)" << std::endl;
    if (oacs & (1 << 9)) std::cout << "  Bit 9: Get LBA Status" << std::endl;

    std::cout << "========================================\n" << std::endl;

    close(fd);
    return dbc_supported;
}

int main() {
    std::cout << "Checking DBC Support on NVMe Devices\n" << std::endl;

    // Check common NVMe device paths
    const char* devices[] = {
        "/dev/nvme0",  // Usually 09:00.0
        "/dev/nvme1",  // Usually 41:00.0
        "/dev/nvme2",
        "/dev/nvme3"
    };

    int found = 0;
    int dbc_count = 0;

    for (const char* dev : devices) {
        if (access(dev, F_OK) == 0) {
            found++;
            if (check_dbc_support(dev)) {
                dbc_count++;
            }
        }
    }

    std::cout << "\nSummary:" << std::endl;
    std::cout << "  Devices checked: " << found << std::endl;
    std::cout << "  Devices with DBC: " << dbc_count << std::endl;

    if (dbc_count > 0) {
        std::cout << "\n✓ At least one device supports DBC!" << std::endl;
        std::cout << "Mode 4 should work with proper implementation." << std::endl;
    } else {
        std::cout << "\n✗ No devices found with DBC support." << std::endl;
        std::cout << "Mode 4 will not work on this system." << std::endl;
    }

    return 0;
}