/**
 * @file feature.h
 * @brief Base class for device feature detection
 *
 * Provides common interface for querying hardware and software capabilities.
 * All feature classes (GPU, NVMe, Host) inherit from this base.
 */

#pragma once
#include "cuda_utils.h"
#include <cstdint>
#include <string>
#include <vector>

using std::string;
using std::vector;

/**
 * @brief Base class for all feature detection
 *
 * Provides common interface for reporting device capabilities and status.
 * Derived classes implement specific detection logic for GPU, NVMe, Host.
 */
class Feature {
public:
    virtual ~Feature() = default;

    /**
     * @brief Check if the feature/device is available
     * @return true if device is present and accessible
     */
    virtual bool is_available() const = 0;

    /**
     * @brief Get human-readable device name
     * @return Device name string (e.g., "NVIDIA RTX 4090", "Samsung 980 PRO")
     */
    virtual string get_name() const = 0;

    /**
     * @brief Get detailed feature description
     * @return Multi-line string describing all capabilities
     */
    virtual string get_description() const = 0;

    /**
     * @brief Print feature information to stdout
     * @param verbose If true, print detailed information
     */
    virtual void print(bool verbose = false) const = 0;
};

/**
 * @brief Support level enumeration
 */
enum class SupportLevel : uint8_t {
    NOT_SUPPORTED = 0,  ///< Feature not available
    HARDWARE_ONLY = 1,  ///< Hardware supports, but software/driver missing
    PARTIAL = 2,        ///< Partially supported (e.g., limited queue count)
    FULL = 3            ///< Fully supported and enabled
};

/**
 * @brief Convert support level to string
 */
inline const char* support_level_str(SupportLevel level) {
    switch (level) {
        case SupportLevel::NOT_SUPPORTED: return "Not Supported";
        case SupportLevel::HARDWARE_ONLY: return "Hardware Only";
        case SupportLevel::PARTIAL:       return "Partial";
        case SupportLevel::FULL:          return "Full";
        default:                          return "Unknown";
    }
}
