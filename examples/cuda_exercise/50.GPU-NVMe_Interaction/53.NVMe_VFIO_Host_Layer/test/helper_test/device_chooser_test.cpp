#include <gtest/gtest.h>

#include "device/device_detector.h"

#include <memory>

namespace {

class DeviceChooserTest : public ::testing::Test {
protected:
    void SetUp() override {
        features_ = SystemFeatures::detect_all();
    }

    SystemFeatures features_{};
};

bool hasSafeNvme(const SystemFeatures& features,
                 const DeviceRequirements& req) {
    for (const auto& nvme : features.nvme_devs) {
        if (!nvme.is_available() || nvme.is_os_live()) {
            continue;
        }
        if (req.require_nvme_vfio && !nvme.has_vfio_binding()) {
            continue;
        }
        if (req.require_shadow_doorbell) {
            auto level = nvme.get_shadow_doorbell_support();
            if (level != SupportLevel::FULL && level != SupportLevel::PARTIAL) {
                continue;
            }
        }
        if (req.require_nvme_p2p &&
            nvme.get_p2p_support() != SupportLevel::FULL) {
            continue;
        }
        if (req.min_nvme_capacity > 0 &&
            nvme.get_capacity_bytes() < req.min_nvme_capacity) {
            continue;
        }
        return true;
    }
    return false;
}

size_t safeNvmeCount(const SystemFeatures& features,
                     const DeviceRequirements& req) {
    size_t count = 0;
    for (const auto& nvme : features.nvme_devs) {
        if (!nvme.is_available() || nvme.is_os_live()) {
            continue;
        }
        if (req.require_nvme_vfio && !nvme.has_vfio_binding()) {
            continue;
        }
        if (req.require_shadow_doorbell) {
            auto level = nvme.get_shadow_doorbell_support();
            if (level != SupportLevel::FULL && level != SupportLevel::PARTIAL) {
                continue;
            }
        }
        if (req.require_nvme_p2p &&
            nvme.get_p2p_support() != SupportLevel::FULL) {
            continue;
        }
        if (req.min_nvme_capacity > 0 &&
            nvme.get_capacity_bytes() < req.min_nvme_capacity) {
            continue;
        }
        ++count;
    }
    return count;
}

}  // namespace

TEST_F(DeviceChooserTest, AlwaysReturnsHostInformation) {
    auto selection = features_.select_devices(DeviceRequirements{});
    ASSERT_NE(selection.host, nullptr);
    EXPECT_EQ(selection.host, &features_.host);
    EXPECT_FALSE(selection.host->get_os_name().empty());
}

TEST_F(DeviceChooserTest, SelectsGpuForComputeRequirements) {
    if (features_.gpus.empty()) {
        GTEST_SUCCEED() << "No GPUs detected on this platform; compute selection not applicable.";
        return;
    }

    auto selection = features_.select_for_gpu_compute();
    if (!selection.gpu) {
        GTEST_SUCCEED() << "No GPU satisfies the compute requirements on this platform.";
        return;
    }

    EXPECT_TRUE(selection.gpu->has_cuda());
    EXPECT_GE(selection.gpu->get_total_memory(), 0ULL);
}

TEST_F(DeviceChooserTest, SelectsUnboundNvmeForHostDma) {
    auto req = DeviceRequirements::for_host_dma();
    req.require_nvme = true;

    auto selection = features_.select_devices(req);
    if (!hasSafeNvme(features_, req)) {
        EXPECT_EQ(selection.nvme, nullptr)
            << "Chooser must not fall back to OS-owned NVMe devices.";
        GTEST_SUCCEED() << "No safe NVMe devices available on this platform.";
        return;
    }

    ASSERT_NE(selection.nvme, nullptr);
    EXPECT_FALSE(selection.nvme->is_os_live())
        << "SystemFeatures should never prefer an OS-owned NVMe when safe drives exist.";
}

TEST_F(DeviceChooserTest, ReturnsAllSafeNvmeMatches) {
    auto req = DeviceRequirements::for_host_dma();
    req.require_nvme = true;

    auto matches = features_.get_matching_nvme(req);
    const size_t expected_safe = safeNvmeCount(features_, req);

    if (expected_safe == 0) {
        EXPECT_TRUE(matches.empty());
        GTEST_SUCCEED() << "No safe NVMe devices meet host-DMA requirements.";
        return;
    }

    ASSERT_EQ(matches.size(), expected_safe);
    for (size_t idx : matches) {
        ASSERT_LT(idx, features_.nvme_devs.size());
        const auto& nvme = features_.nvme_devs[idx];
        EXPECT_FALSE(nvme.is_os_live());
    }
}

TEST_F(DeviceChooserTest, PrefersShadowDoorbellCapableNvmeWhenPresent) {
    // Use host-DMA requirements to avoid over-constraining selection
    auto req = DeviceRequirements::for_host_dma();
    req.require_nvme = true;

    // Identify first DBC-capable NVMe (shadow doorbell FULL) that is safe to use
    std::optional<size_t> first_dbc_idx;
    for (size_t i = 0; i < features_.nvme_devs.size(); ++i) {
        const auto& nvme = features_.nvme_devs[i];
        if (!nvme.is_available() || nvme.is_os_live()) continue;
        if (nvme.get_shadow_doorbell_support() == SupportLevel::FULL) {
            first_dbc_idx = i;
            break;
        }
    }

    auto matches = features_.get_matching_nvme(req);

    if (!first_dbc_idx.has_value() || matches.empty()) {
        GTEST_SUCCEED() << "No DBC-capable NVMe available (or no safe NVMe); preference check not applicable.";
        return;
    }

    ASSERT_LT(first_dbc_idx.value(), features_.nvme_devs.size());
    EXPECT_EQ(matches.front(), first_dbc_idx.value())
        << "Device chooser should prioritize shadow-doorbell (DBC) NVMe devices first.";
}
