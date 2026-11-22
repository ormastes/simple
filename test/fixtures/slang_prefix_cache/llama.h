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
enum llama_pooling_type { LLAMA_POOLING_TYPE_UNSPECIFIED = -1, LLAMA_POOLING_TYPE_NONE = 0, LLAMA_POOLING_TYPE_MEAN = 1, LLAMA_POOLING_TYPE_CLS = 2, LLAMA_POOLING_TYPE_LAST = 3, LLAMA_POOLING_TYPE_RANK = 4 };
#define LLAMA_TOKEN_NULL -1
struct llama_context_params { uint32_t n_ctx; uint32_t n_batch; uint32_t n_ubatch; uint32_t n_seq_max; bool kv_unified; int32_t n_threads; int32_t n_threads_batch; enum llama_pooling_type pooling_type; bool embeddings; };
struct llama_sampler_chain_params { int unused; };
struct llama_batch { llama_token * token; int32_t n_tokens; llama_pos * pos; int32_t * n_seq_id; llama_seq_id ** seq_id; int8_t * logits; };
struct llama_chat_message { const char * role; const char * content; };
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
uint32_t llama_n_ubatch(const struct llama_context *);
bool llama_supports_gpu_offload(void);
const char * llama_model_chat_template(const struct llama_model *, const char *);
int32_t llama_chat_apply_template(const char *, const struct llama_chat_message *, size_t, bool, char *, int32_t);
const struct llama_vocab * llama_model_get_vocab(const struct llama_model *);
int32_t llama_vocab_n_tokens(const struct llama_vocab *);
float * llama_get_logits_ith(struct llama_context *, int32_t);
int32_t llama_tokenize(const struct llama_vocab *, const char *, int32_t,
                       llama_token *, int32_t, bool, bool);
bool llama_vocab_is_eog(const struct llama_vocab *, llama_token);
int32_t llama_token_to_piece(const struct llama_vocab *, llama_token, char *,
                             int32_t, int32_t, bool);
llama_memory_t llama_get_memory(const struct llama_context *);
void llama_memory_clear(llama_memory_t, bool);
bool llama_memory_seq_rm(llama_memory_t, llama_seq_id, llama_pos, llama_pos);
llama_pos llama_memory_seq_pos_min(llama_memory_t, llama_seq_id);
llama_pos llama_memory_seq_pos_max(llama_memory_t, llama_seq_id);
size_t llama_state_seq_get_size(struct llama_context *, llama_seq_id);
size_t llama_state_seq_get_data(struct llama_context *, uint8_t *, size_t, llama_seq_id);
size_t llama_state_seq_set_data(struct llama_context *, const uint8_t *, size_t, llama_seq_id);
struct llama_batch llama_batch_get_one(llama_token *, int32_t);
struct llama_batch llama_batch_init(int32_t, int32_t, int32_t);
void llama_batch_free(struct llama_batch);
void llama_memory_seq_cp(llama_memory_t, llama_seq_id, llama_seq_id, llama_pos, llama_pos);
int32_t llama_decode(struct llama_context *, struct llama_batch);
llama_token llama_sampler_sample(struct llama_sampler *, struct llama_context *, int32_t);
enum llama_pooling_type llama_pooling_type(const struct llama_context *);
float * llama_get_embeddings(struct llama_context *);
float * llama_get_embeddings_seq(struct llama_context *, llama_seq_id);
int32_t llama_model_n_embd_out(const struct llama_model *);
uint32_t llama_model_n_cls_out(const struct llama_model *);
int32_t llama_model_n_ctx_train(const struct llama_model *);
llama_token llama_vocab_bos(const struct llama_vocab *);
llama_token llama_vocab_eos(const struct llama_vocab *);
llama_token llama_vocab_sep(const struct llama_vocab *);
bool llama_vocab_get_add_bos(const struct llama_vocab *);
bool llama_vocab_get_add_eos(const struct llama_vocab *);
bool llama_vocab_get_add_sep(const struct llama_vocab *);
#define LLAMA_DEFAULT_SEED 0xFFFFFFFF
struct llama_sampler * llama_sampler_init_penalties(int32_t, int32_t, float, float, float);
struct llama_sampler * llama_sampler_init_top_k(int32_t);
struct llama_sampler * llama_sampler_init_top_p(float, size_t);
struct llama_sampler * llama_sampler_init_temp(float);
struct llama_sampler * llama_sampler_init_dist(uint32_t);
#endif
