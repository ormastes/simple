#include "feature_matrix.h"

#include <sstream>

namespace features59 {

std::string formatMatrix(const FeatureMatrix& matrix) {
    std::ostringstream oss;
    oss << "Module 59 feature matrix (" << matrix.featureCount() << " entries)\n";
    std::size_t index = 1;
    for (const auto& entry : matrix.entries) {
        oss << "  [" << index++ << "] " << entry.name << " | "
            << entry.support << " | Layer: " << entry.source_layer.name
            << " | " << entry.notes << '\n';
    }
    return oss.str();
}

}  // namespace features59
