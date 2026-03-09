#include "dataset_routes.h"

namespace dataset59 {
namespace {

DatasetRoute make_route(const std::string& name,
                        const std::string& device,
                        const std::string& shape,
                        const testing59::TestEntry& entry) {
    return DatasetRoute{name, device, shape, entry};
}

}  // namespace

DatasetPlan buildDatasetPlan() {
    const auto tests = testing59::buildTestMatrix();
    DatasetPlan plan;
    plan.routes = {
        make_route("Expert Weights", "/dev/nvme0n1", "[num_experts, hidden, ffn]",
                   tests.entries[2]),
        make_route("Attention Activations", "/dev/nvme1n1", "[batch, seq, hidden]",
                   tests.entries[0]),
        make_route("Training Dataset Shards", "/mnt/nvme/training.bin", "[shard, token, dim]",
                   tests.entries[1]),
    };
    return plan;
}

}  // namespace dataset59
