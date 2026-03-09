/**
 * @file detect_dbc_support.cpp
 * @brief Utility to detect NVMe DBC (Doorbell Buffer Config) support
 *
 * This is a simple CLI wrapper around NvmeFeature to check DBC support.
 */

#include "device/nvme_feature.h"
#include <iostream>

int main() {
    std::cout << "=== NVMe DBC Support Detection Utility ===\n\n";

    auto devices = get_all_nvme_devices();

    if (devices.empty()) {
        std::cout << "No NVMe devices found.\n";
        std::cout << "Note: You may need root permissions to access /dev/nvme*\n";
        return 1;
    }

    std::cout << "Found " << devices.size() << " NVMe device(s):\n\n";

    int dbc_count = 0;

    for (const auto& dev : devices) {
        std::cout << "Device: " << dev.get_device_path() << "\n";

        if (!dev.is_available()) {
            std::cout << "  Status: NOT ACCESSIBLE\n";
            std::cout << "  Hint: Try running with sudo\n\n";
            continue;
        }

        std::cout << "  Model:  " << dev.get_model() << "\n";
        std::cout << "  NVMe:   " << (int)dev.get_nvme_version_major() << "."
                  << (int)dev.get_nvme_version_minor() << "\n";
        std::cout << "  OACS:   0x" << std::hex << dev.get_oacs() << std::dec << "\n";
        std::cout << "  DBC:    ";

        if (dev.get_shadow_doorbell_support() == SupportLevel::FULL) {
            std::cout << "\033[1;32mSUPPORTED\033[0m ✓\n";
            std::cout << "  --> This device supports hardware DBC (bit 8 of OACS is set)\n";
            dbc_count++;
        } else {
            std::cout << "\033[1;31mNOT SUPPORTED\033[0m ✗\n";
            std::cout << "  --> This device does NOT support hardware DBC\n";
        }

        std::cout << "\n";
    }

    std::cout << "=== Summary ===\n";
    std::cout << "Total devices: " << devices.size() << "\n";
    std::cout << "DBC-capable:   " << dbc_count << "\n";

    if (dbc_count > 0) {
        std::cout << "\n\033[1;32m✓ You have " << dbc_count
                  << " device(s) that support hardware DBC!\033[0m\n";
    } else {
        std::cout << "\n\033[1;33m⚠ None of your devices support hardware DBC.\033[0m\n";
    }

    return 0;
}
