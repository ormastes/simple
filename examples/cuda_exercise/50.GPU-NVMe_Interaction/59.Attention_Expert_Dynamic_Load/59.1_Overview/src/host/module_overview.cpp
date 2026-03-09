#include "overview_data.h"

#include <array>

namespace overview59 {

namespace {

OverviewComponent make_component(std::string name, std::string description) {
    return OverviewComponent{std::move(name), std::move(description)};
}

}  // namespace

OverviewSummary buildDefaultOverview() {
    OverviewSummary summary;
    summary.module_name = "59.1 Overview";
    summary.components = {
        make_component("Python API Layer",
                       "attention_expert/ops.py provides nn.Module wrappers and "
                       "NVMe-aware helpers."),
        make_component("PyTorch Dispatcher Layer",
                       "Dispatcher, autograd, and autocast implementations "
                       "registered via TORCH_LIBRARY."),
        make_component("CUDA Kernel Layer",
                       "attention_fwd.cu and expert_fwd.cu implement attention "
                       "and Mixture-of-Experts kernels."),
        make_component("Storage + Metadata Layer",
                       "Common headers and TensorNVMeReader coordinate NVMe-backed "
                       "weight loading."),
    };
    return summary;
}

}  // namespace overview59
