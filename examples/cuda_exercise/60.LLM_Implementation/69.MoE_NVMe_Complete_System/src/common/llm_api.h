/**
 * @file llm_api.h
 * @brief C API for the complete LLM system
 *
 * Provides a stable C interface for creating, running, and destroying
 * LLM models. This API hides all C++ and CUDA internals behind an
 * opaque handle, making it suitable for integration with other
 * languages (Python, Rust, etc.) via FFI.
 */
#pragma once

#ifdef __cplusplus
extern "C" {
#endif

/// Opaque model handle
typedef void* LLMModel;

/**
 * @brief Create and initialize a model from a configuration file
 *
 * Parses the configuration, allocates GPU resources, and optionally
 * loads pretrained weights. The returned handle must be freed with
 * llm_destroy_model().
 *
 * @param[in] config_path  Path to JSON/YAML model configuration file
 * @return Opaque model handle, or NULL on failure
 */
LLMModel llm_create_model(const char* config_path);

/**
 * @brief Generate text autoregressively from input token IDs
 *
 * Runs the forward pass in a loop, appending generated tokens until
 * max_output_len is reached or an end-of-sequence token is produced.
 *
 * @param[in]  model          Opaque model handle
 * @param[in]  input_ids      Input token ID array
 * @param[in]  input_len      Number of input tokens
 * @param[out] output_ids     Output buffer for generated token IDs
 * @param[in]  max_output_len Maximum number of tokens to generate
 * @return Number of tokens actually generated, or -1 on error
 */
int llm_generate(LLMModel model, const int* input_ids, int input_len,
                int* output_ids, int max_output_len);

/**
 * @brief Destroy a model and free all associated resources
 * @param[in] model  Opaque model handle (safe to pass NULL)
 */
void llm_destroy_model(LLMModel model);

/**
 * @brief Get the vocabulary size of the model
 * @param[in] model  Opaque model handle
 * @return Vocabulary size, or -1 on error
 */
int llm_get_vocab_size(LLMModel model);

/**
 * @brief Get the maximum sequence length supported by the model
 * @param[in] model  Opaque model handle
 * @return Maximum sequence length, or -1 on error
 */
int llm_get_max_seq_len(LLMModel model);

/**
 * @brief Get the total number of model parameters
 * @param[in] model  Opaque model handle
 * @return Number of parameters, or -1 on error
 */
long long llm_get_num_parameters(LLMModel model);

#ifdef __cplusplus
}
#endif
