#include "test_matrix.h"

#include <sstream>

namespace testing59 {

std::string formatMatrix(const TestMatrix& matrix) {
    std::ostringstream oss;
    oss << "Testing Matrix (" << matrix.testCount() << " entries)\n";
    std::size_t idx = 1;
    for (const auto& entry : matrix.entries) {
        oss << "  [" << idx++ << "] " << entry.name << " [" << entry.type << "]\n"
            << "      Command: " << entry.command << "\n"
            << "      Scenario: " << entry.scenario.name << '\n';
    }
    return oss.str();
}

}  // namespace testing59
