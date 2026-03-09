/**
 * @file cli_template.h
 * @brief Template-based CLI utility for Module 59
 */

#pragma once

#include <cuda_runtime.h>
#include <iostream>
#include <string>
#include <functional>

namespace module59 {
namespace cli {

/**
 * @brief Generic CLI runner template
 * @tparam T The data type being built and formatted
 */
template<typename T>
class CLIRunner {
public:
    using BuilderFunc = std::function<T()>;
    using FormatterFunc = std::function<std::string(const T&)>;
    using DevicePopulatorFunc = std::function<void(int*, int)>;
    using CountExtractorFunc = std::function<int(const T&)>;

    struct Config {
        BuilderFunc builder;
        FormatterFunc formatter;
        DevicePopulatorFunc device_populator;
        CountExtractorFunc count_extractor;
        std::string item_name;
    };

    static int run(const Config& config) {
        // Build the data object
        const auto data = config.builder();

        // Format and print the data
        std::cout << config.formatter(data) << std::endl;

        // CUDA device operations
        int* device_value = nullptr;
        cudaMalloc(&device_value, sizeof(int));

        const int count = config.count_extractor(data);
        config.device_populator(device_value, count);

        int host_value = 0;
        cudaMemcpy(&host_value, device_value, sizeof(int), cudaMemcpyDeviceToHost);
        cudaFree(device_value);

        std::cout << "Kernel reported " << host_value << " " << config.item_name << "." << std::endl;

        return 0;
    }
};

// Macro for quick CLI generation
#define MODULE59_CLI_MAIN(Namespace, Type, ItemName) \
int main() { \
    using namespace Namespace; \
    module59::cli::CLIRunner<Type>::Config config{ \
        .builder = build##Type, \
        .formatter = format##Type, \
        .device_populator = populateDevice##Type##Count, \
        .count_extractor = [](const Type& t) { return static_cast<int>(t.ItemName##Count()); }, \
        .item_name = #ItemName "s" \
    }; \
    return module59::cli::CLIRunner<Type>::run(config); \
}

} // namespace cli
} // namespace module59