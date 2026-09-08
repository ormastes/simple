#ifndef TEST_LLAMA_H
#define TEST_LLAMA_H
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
typedef int32_t llama_token;
typedef int32_t llama_seq_id;
typedef int32_t llama_pos;
typedef void * llama_memory_t;
struct llama_model;
struct llama_context;
struct llama_sampler;
struct llama_vocab;
struct llama_model_params { int32_t n_gpu_layers; };
struct llama_context_params { uint32_t n_ctx; uint32_t n_batch; };
struct llama_sampler_chain_params { int unused; };
struct llama_batch { llama_token * token; int32_t n_tokens; };
void llama_backend_init(void);
struct llama_model_params llama_model_default_params(void);
struct llama_model * llama_model_load_from_file(const char *, struct llama_model_params);
struct llama_context_params llama_context_default_params(void);
struct llama_context * llama_init_from_model(struct llama_model *, struct llama_context_params);
struct llama_sampler_chain_params llama_sampler_chain_default_params(void);
struct llama_sampler * llama_sampler_chain_init(struct llama_sampler_chain_params);
struct llama_sampler * llama_sampler_init_greedy(void);
void llama_sampler_chain_add(struct llama_sampler *, struct llama_sampler *);
void llama_sampler_free(struct llama_sampler *);
void llama_free(struct llama_context *);
void llama_model_free(struct llama_model *);
uint32_t llama_n_ctx(const struct llama_context *);
const struct llama_vocab * llama_model_get_vocab(const struct llama_model *);
int32_t llama_tokenize(const struct llama_vocab *, const char *, int32_t,
                       llama_token *, int32_t, bool, bool);
bool llama_vocab_is_eog(const struct llama_vocab *, llama_token);
int32_t llama_token_to_piece(const struct llama_vocab *, llama_token, char *,
                             int32_t, int32_t, bool);
llama_memory_t llama_get_memory(const struct llama_context *);
void llama_memory_clear(llama_memory_t, bool);
bool llama_memory_seq_rm(llama_memory_t, llama_seq_id, llama_pos, llama_pos);
size_t llama_state_seq_get_size(struct llama_context *, llama_seq_id);
size_t llama_state_seq_get_data(struct llama_context *, uint8_t *, size_t, llama_seq_id);
size_t llama_state_seq_set_data(struct llama_context *, const uint8_t *, size_t, llama_seq_id);
struct llama_batch llama_batch_get_one(llama_token *, int32_t);
int32_t llama_decode(struct llama_context *, struct llama_batch);
llama_token llama_sampler_sample(struct llama_sampler *, struct llama_context *, int32_t);
#endif
