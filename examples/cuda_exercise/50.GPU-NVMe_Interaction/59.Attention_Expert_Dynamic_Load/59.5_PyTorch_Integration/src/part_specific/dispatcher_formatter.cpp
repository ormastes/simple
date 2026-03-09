#include "dispatcher_checks.h"

#include <sstream>

namespace torch59 {

std::string formatMatrix(const DispatcherMatrix& matrix) {
    std::ostringstream oss;
    oss << "PyTorch Integration Checks (" << matrix.checkCount() << " entries)\n";
    std::size_t idx = 1;
    for (const auto& check : matrix.checks) {
        oss << "  [" << idx++ << "] " << check.name << " "
            << check.status << " via " << check.dispatch_key << "\n"
            << "      Example: " << check.reference_example.file_path << '\n';
    }
    return oss.str();
}

}  // namespace torch59
