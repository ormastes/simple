/**
 * @file question_answering.cpp
 * @brief Question-answering demo using the LLM C API with prompt templates
 *
 * Demonstrates a QA workflow: constructing a prompt template,
 * encoding it as token IDs, generating a response, and displaying
 * the result. In production, a tokenizer would handle text-to-ID
 * and ID-to-text conversion.
 */

#include "common/llm_api.h"
#include <cstdio>
#include <cstdlib>
#include <cstring>

/// Simulated prompt template encoding (placeholder for tokenizer)
static int encode_qa_prompt(const char* question, int* output_ids, int max_len) {
    // Simple hash-based encoding for demonstration
    int len = 0;
    // Add "Question:" prefix tokens
    output_ids[len++] = 101;  // [CLS] or prompt start
    output_ids[len++] = 2953; // "Question"
    output_ids[len++] = 25;   // ":"

    // Encode each character as a token (simplified)
    for (int i = 0; question[i] != '\0' && len < max_len - 2; ++i) {
        output_ids[len++] = (unsigned char)question[i];
    }

    // Add "Answer:" suffix tokens
    output_ids[len++] = 3280; // "Answer"
    output_ids[len++] = 25;   // ":"

    return len;
}

int main(int argc, char** argv) {
    const char* config_path = (argc > 1) ? argv[1] : "model_config.txt";
    const char* question = (argc > 2) ? argv[2] : "What is a Mixture of Experts model?";

    printf("=== Question Answering Demo ===\n");
    printf("Config: %s\n", config_path);
    printf("Question: %s\n\n", question);

    // Create model
    LLMModel model = llm_create_model(config_path);
    if (!model) {
        fprintf(stderr, "Failed to create model from config: %s\n", config_path);
        return 1;
    }

    printf("Model loaded (%lld parameters)\n\n", llm_get_num_parameters(model));

    // Encode the question as a prompt
    int max_prompt_len = 128;
    int* prompt_ids = new int[max_prompt_len];
    int prompt_len = encode_qa_prompt(question, prompt_ids, max_prompt_len);

    printf("Prompt tokens (%d): [", prompt_len);
    for (int i = 0; i < prompt_len && i < 10; ++i) {
        printf("%d%s", prompt_ids[i], (i < prompt_len - 1 && i < 9) ? ", " : "");
    }
    if (prompt_len > 10) printf(", ...");
    printf("]\n\n");

    // Generate answer
    int max_answer = 50;
    int* answer_ids = new int[max_answer];
    int generated = llm_generate(model, prompt_ids, prompt_len, answer_ids, max_answer);

    if (generated > 0) {
        printf("Answer tokens (%d): [", generated);
        for (int i = 0; i < generated && i < 10; ++i) {
            printf("%d%s", answer_ids[i], (i < generated - 1 && i < 9) ? ", " : "");
        }
        if (generated > 10) printf(", ...");
        printf("]\n");
        printf("\n(In a full system, these tokens would be decoded back to text)\n");
    } else {
        printf("Generation failed (returned %d)\n", generated);
    }

    // Cleanup
    delete[] prompt_ids;
    delete[] answer_ids;
    llm_destroy_model(model);

    printf("\nDone.\n");
    return 0;
}
