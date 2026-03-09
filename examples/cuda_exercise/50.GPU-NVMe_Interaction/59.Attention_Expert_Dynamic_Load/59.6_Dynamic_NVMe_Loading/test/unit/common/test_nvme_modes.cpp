#include <gtest/gtest.h>

#include "nvme_modes.h"

namespace {

using nvme59::buildNvmeModes;

TEST(NvmeModesTest, IncludesDynamicAllMode) {
    const auto modes = buildNvmeModes();
    bool found_dynamic_all = false;
    for (const auto& mode : modes.modes) {
        if (mode.name == "DYNAMIC_ALL") {
            found_dynamic_all = true;
        }
    }
    EXPECT_TRUE(found_dynamic_all);
}

TEST(NvmeModesTest, ModeCountAtLeastThree) {
    const auto modes = buildNvmeModes();
    EXPECT_GE(modes.modeCount(), 3u);
}

}  // namespace
