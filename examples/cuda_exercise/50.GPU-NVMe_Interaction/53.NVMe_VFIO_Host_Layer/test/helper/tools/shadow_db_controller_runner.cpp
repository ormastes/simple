/**
 * @file shadow_db_controller_runner.cpp
 * @brief Minimal launcher for ShadowDbControllerTask to mirror shadow DB -> MMIO doorbells
 *
 * Usage:
 *   shadow_db_controller_runner <NVME_BDF> <NSID> <LBA_SIZE> <SLBA>
 *
 * This is intended as a safety net when hardware DBC polling is unavailable.
 */

#include "setup_helper.h"
#include <iostream>
#include <string>
#include <thread>

int main(int argc, char** argv) {
    if (argc < 5) {
        std::cerr << "Usage: " << argv[0] << " <NVME_BDF> <NSID> <LBA_SIZE> <SLBA>\n";
        return 1;
    }

    std::string bdf = argv[1];
    std::string nsid = argv[2];
    std::string lba_size = argv[3];
    std::string slba = argv[4];

    SetupHelper helper;
    helper.set_global_args({
        {"NVME_BDF", bdf},
        {"NVME_NSID", nsid},
        {"NVME_LBA_SIZE", lba_size},
        {"NVME_SLBA", slba},
        {"queue_count", "1"},
        {"queue_id", "1"}
    });

    // Build minimal task chain: NVMe open -> shadow buffer -> shadow controller
    helper.add_task(new NvmeSetupTask(bdf));
    helper.add_task(new DbcShadowBufferTask(1, false, 1));
    helper.add_task(new ShadowDbControllerTask(1));

    if (!helper.setup_all()) {
        std::cerr << "Failed to start ShadowDbControllerTask\n";
        return 2;
    }

    std::cout << "ShadowDbControllerTask is running. Press Ctrl+C to exit.\n";
    // Block forever; the daemon thread runs until process exit.
    while (true) {
        std::this_thread::sleep_for(std::chrono::seconds(10));
    }

    return 0;
}
