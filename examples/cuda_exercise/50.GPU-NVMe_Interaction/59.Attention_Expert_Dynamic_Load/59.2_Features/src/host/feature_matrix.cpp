#include "feature_matrix.h"

namespace features59 {
namespace {

FeatureEntry make_entry(const std::string& name,
                        const std::string& support,
                        const std::string& notes,
                        const overview59::OverviewComponent& source) {
    return FeatureEntry{name, support, notes, source};
}

}  // namespace

FeatureMatrix buildDefaultMatrix() {
    const auto overview = overview59::buildDefaultOverview();
    FeatureMatrix matrix;

    matrix.entries = {
        make_entry("Autograd Support", "✅ Full",
                   "Uses torch::autograd::Function in dispatcher layer.",
                   overview.components[1]),
        make_entry("AMP / Autocast", "✅ Full",
                   "Autocast backend ensures FP16/BF16 coverage.",
                   overview.components[1]),
        make_entry("torch.compile", "✅ Full",
                   "Dispatcher registration makes ops Dynamo friendly.",
                   overview.components[1]),
        make_entry("Nvme Load Modes", "✅ Full",
                   "ALL_IN_MEMORY, DYNAMIC_FFN_ONLY, DYNAMIC_ALL.",
                   overview.components[3]),
        make_entry("MoE Routing", "✅ Full",
                   "Top-K routing, capacity factor checks.",
                   overview.components[2]),
        make_entry("Python nn.Modules", "✅ Full",
                   "Drop-in wrappers for attention/MoE in ops.py.",
                   overview.components[0]),
        make_entry("Integration Testing Hooks", "⚠️ Disabled by default",
                   "CTest entries added but disabled pending fixtures.",
                   overview.components[0]),
    };
    return matrix;
}

}  // namespace features59
