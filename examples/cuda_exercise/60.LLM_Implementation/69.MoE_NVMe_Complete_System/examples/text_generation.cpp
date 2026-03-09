/**
 * @file text_generation.cpp
 * @brief Simple text generation demo using the LLM C API
 *
 * Demonstrates creating a model, generating tokens from a prompt,
 * and cleaning up resources. In a full system the token IDs would
 * be converted to/from text via a tokenizer.
 */

#include "common/llm_api.h"
#include <cstdio>
#include <cstdlib>

int main(int argc, char** argv) {
    const char* config_path = (argc > 1) ? argv[1] : "model_config.txt";

    printf("=== Text Generation Demo ===\n");
    printf("Config: %s\n\n", config_path);

    // Create model
    LLMModel model = llm_create_model(config_path);
    if (!model) {
        fprintf(stderr, "Failed to create model from config: %s\n", config_path);
        return 1;
    }

    printf("Model created:\n");
    printf("  Vocab size:     %d\n", llm_get_vocab_size(model));
    printf("  Max seq len:    %d\n", llm_get_max_seq_len(model));
    printf("  Parameters:     %lld\n\n", llm_get_num_parameters(model));

    // Simulate input prompt (token IDs)
    int input_ids[] = {1, 42, 100, 256, 500};
    int input_len = 5;

    printf("Input token IDs: [");
    for (int i = 0; i < input_len; ++i) {
        printf("%d%s", input_ids[i], (i < input_len - 1) ? ", " : "");
    }
    printf("]\n\n");

    // Generate output
    int max_output = 20;
    int* output_ids = new int[max_output];

    int generated = llm_generate(model, input_ids, input_len, output_ids, max_output);

    if (generated > 0) {
        printf("Generated %d tokens:\n  [", generated);
        for (int i = 0; i < generated; ++i) {
            printf("%d%s", output_ids[i], (i < generated - 1) ? ", " : "");
        }
        printf("]\n");
    } else {
        printf("Generation failed (returned %d)\n", generated);
    }

    // Cleanup
    delete[] output_ids;
    llm_destroy_model(model);

    printf("\nDone.\n");
    return 0;
}
