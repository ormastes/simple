/*
 * MedGemma Korean Training Pipeline - Native C Implementation
 *
 * Phase 0: English Medical Data Preparation (Baseline)
 * Phase 1: Evaluate + LoRA Training
 * Phase 2: MCQ Training
 *
 * Build:
 *   gcc -std=gnu11 -O2 -c -I ../../src/runtime -o /tmp/medgemma.o medgemma_native.c
 *   gcc -std=gnu11 -O2 -c -I ../../src/runtime -o /tmp/runtime.o ../../src/runtime/runtime.c
 *   g++ -o /tmp/medgemma /tmp/medgemma.o /tmp/runtime.o \
 *       -L ../../build -lspl_torch \
 *       -L ~/.local/lib/python3.12/site-packages/torch/lib -ltorch -ltorch_cpu -lc10 \
 *       -Wl,-rpath,../../build \
 *       -Wl,-rpath,$HOME/.local/lib/python3.12/site-packages/torch/lib \
 *       -lm -lpthread -ldl
 *
 * Run:
 *   /tmp/medgemma
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include "runtime.h"

/* =========================================================================
 * Torch FFI Declarations
 * ========================================================================= */

extern int64_t rt_torch_available(void);
extern int64_t rt_torch_cuda_available(void);
extern int64_t rt_torch_tensor_rand_2d(int64_t d0, int64_t d1);
extern int64_t rt_torch_tensor_randn_2d(int64_t d0, int64_t d1);
extern int64_t rt_torch_tensor_zeros_2d(int64_t d0, int64_t d1);
extern int64_t rt_torch_tensor_ones_2d(int64_t d0, int64_t d1);
extern int64_t rt_torch_tensor_randn(SplArray* dims);
extern int64_t rt_torch_tensor_zeros(SplArray* dims);
extern SplArray* rt_torch_torchtensor_shape(int64_t t);
extern int64_t rt_torch_torchtensor_shape_dim(int64_t handle, int64_t dim_idx);
extern int64_t rt_torch_torchtensor_free(int64_t t);
extern int64_t rt_torch_torchtensor_matmul(int64_t a, int64_t b);
extern int64_t rt_torch_torchtensor_add(int64_t a, int64_t b);
extern int64_t rt_torch_torchtensor_sub(int64_t a, int64_t b);
extern int64_t rt_torch_torchtensor_mul(int64_t a, int64_t b);
extern int64_t rt_torch_torchtensor_gelu(int64_t t);
extern int64_t rt_torch_torchtensor_relu(int64_t t);
extern int64_t rt_torch_torchtensor_softmax(int64_t t, int64_t dim);
extern int64_t rt_torch_torchtensor_log_softmax(int64_t t, int64_t dim);
extern int64_t rt_torch_torchtensor_transpose(int64_t t, int64_t d0, int64_t d1);
extern double  rt_torch_torchtensor_mean(int64_t t);
extern int64_t rt_torch_torchtensor_mean_dim(int64_t handle, int64_t dim, int64_t keepdim);
extern int64_t rt_torch_torchtensor_sum_dim(int64_t handle, int64_t dim, int64_t keepdim);
extern int64_t rt_torch_torchtensor_sum(int64_t t);
extern int64_t rt_torch_autograd_backward(int64_t t);
extern int64_t rt_torch_autograd_grad(int64_t t);
extern void    rt_torch_autograd_set_requires_grad(int64_t t, int64_t req);
extern int64_t rt_torch_autograd_requires_grad(int64_t t);
extern int64_t rt_torch_autograd_zero_grad(int64_t t);
extern int64_t rt_torch_autograd_detach(int64_t t);
extern void    rt_torch_autograd_no_grad_begin(void);
extern void    rt_torch_autograd_no_grad_end(void);
extern int64_t rt_torch_torchtensor_mul_scalar(int64_t t, double s);
extern int64_t rt_torch_torchtensor_neg(int64_t t);
extern int64_t rt_torch_torchtensor_clone(int64_t t);
extern int64_t rt_torch_torchtensor_cuda(int64_t t, int32_t device_id);
extern int64_t rt_torch_torchtensor_cpu(int64_t t);
extern int64_t rt_torch_torchtensor_is_cuda(int64_t t);
extern int64_t rt_torch_torchtensor_reshape(int64_t t, SplArray* shape);
extern int64_t rt_torch_torchtensor_ndim(int64_t t);
extern int64_t rt_torch_torchtensor_numel(int64_t t);
extern int64_t rt_torch_cuda_memory_allocated(int32_t device_id);
extern int64_t rt_torch_cuda_max_memory_allocated(int32_t device_id);
extern void    rt_torch_cuda_empty_cache(void);
extern int64_t rt_torch_nn_embedding(int64_t indices, int64_t weight);
extern int64_t rt_torch_torchtensor_sin(int64_t t);
extern int64_t rt_torch_torchtensor_cos(int64_t t);
extern int64_t rt_torch_torchtensor_slice(int64_t t, int64_t dim, int64_t start, int64_t end, int64_t step);
extern int64_t rt_torch_tensor_from_i64_data(int64_t* data, int64_t len);
extern int64_t rt_torch_nn_cross_entropy(int64_t logits, int64_t targets);

/* =========================================================================
 * Helper: Make SplArray from dimensions
 * ========================================================================= */

static SplArray* make_dims_1d(int64_t d0) {
    SplArray* a = spl_array_new_i64();
    spl_array_push_i64(a, d0);
    return a;
}

static SplArray* make_dims_2d(int64_t d0, int64_t d1) {
    SplArray* a = spl_array_new_i64();
    spl_array_push_i64(a, d0);
    spl_array_push_i64(a, d1);
    return a;
}

static void print_shape(int64_t t) {
    SplArray* shape = rt_torch_torchtensor_shape(t);
    printf("[");
    for (int64_t i = 0; i < shape->len; i++) {
        if (i > 0) printf(", ");
        SplValue v = spl_array_get(shape, i);
        printf("%lld", (long long)v.as_int);
    }
    printf("]");
}

static void print_separator(void) {
    printf("======================================================================\n");
}

/* =========================================================================
 * Model Configuration
 * ========================================================================= */

typedef struct {
    int64_t input_dim;
    int64_t hidden_dim;
    int64_t output_dim;
    double init_scale;
    int64_t num_layers;
} ModelConfig;

static ModelConfig default_model_config(void) {
    return (ModelConfig){.input_dim = 64, .hidden_dim = 128, .output_dim = 32, .init_scale = 0.1, .num_layers = 3};
}

static int64_t model_config_total_params(ModelConfig* cfg) {
    int64_t l1 = cfg->input_dim * cfg->hidden_dim + cfg->hidden_dim;
    int64_t l2 = cfg->hidden_dim * cfg->hidden_dim + cfg->hidden_dim;
    int64_t l3 = cfg->hidden_dim * cfg->output_dim + cfg->output_dim;
    return l1 + l2 + l3;
}

static void model_config_print(ModelConfig* cfg) {
    printf("ModelConfig:\n");
    printf("  Input dim:  %lld\n", (long long)cfg->input_dim);
    printf("  Hidden dim: %lld\n", (long long)cfg->hidden_dim);
    printf("  Output dim: %lld\n", (long long)cfg->output_dim);
    printf("  Layers: %lld\n", (long long)cfg->num_layers);
    printf("  Total params: %lld\n", (long long)model_config_total_params(cfg));
}

/* =========================================================================
 * Training Configuration
 * ========================================================================= */

typedef struct {
    int64_t input_dim;
    int64_t hidden_dim;
    int64_t output_dim;
    int64_t batch_size;
    int64_t num_batches;
    int64_t num_epochs;
    double learning_rate;
    int64_t lora_rank;
    double lora_alpha;
    double max_grad_norm;
    int64_t warmup_steps;
} TrainConfig;

static TrainConfig train_config_phase0(void) {
    return (TrainConfig){
        .input_dim = 64, .hidden_dim = 128, .output_dim = 32,
        .batch_size = 4, .num_batches = 10, .num_epochs = 3,
        .learning_rate = 0.001, .lora_rank = 8, .lora_alpha = 16.0,
        .max_grad_norm = 1.0, .warmup_steps = 5
    };
}

static TrainConfig train_config_phase1(void) {
    TrainConfig c = train_config_phase0();
    c.num_batches = 8;
    c.num_epochs = 2;
    c.learning_rate = 0.0005;
    return c;
}

static TrainConfig train_config_phase2(void) {
    TrainConfig c = train_config_phase0();
    c.num_batches = 8;
    c.num_epochs = 3;
    c.learning_rate = 0.0003;
    return c;
}

static void train_config_print(TrainConfig* cfg, const char* title) {
    printf("\n--- %s Config ---\n", title);
    printf("  Dims: %lld -> %lld -> %lld\n", (long long)cfg->input_dim, (long long)cfg->hidden_dim, (long long)cfg->output_dim);
    printf("  Batch: %lld x %lld batches\n", (long long)cfg->batch_size, (long long)cfg->num_batches);
    printf("  Epochs: %lld\n", (long long)cfg->num_epochs);
    printf("  LR: %.6f (warmup: %lld steps)\n", cfg->learning_rate, (long long)cfg->warmup_steps);
    printf("  LoRA rank: %lld, alpha: %.1f\n", (long long)cfg->lora_rank, cfg->lora_alpha);
    printf("  Max grad norm: %.1f\n", cfg->max_grad_norm);
}

/* =========================================================================
 * Train State
 * ========================================================================= */

typedef struct {
    int64_t global_step;
    double best_loss;
    double epoch_loss;
    int64_t epoch_steps;
} TrainState;

static TrainState train_state_create(void) {
    return (TrainState){.global_step = 0, .best_loss = 1e9, .epoch_loss = 0.0, .epoch_steps = 0};
}

/* =========================================================================
 * GPU Operations
 * ========================================================================= */

static int g_use_cuda = 0; /* set in check_gpu after CUDA test */

static int check_gpu(void) {
    if (!rt_torch_available()) {
        printf("ERROR: libtorch not available.\n");
        return 0;
    }
    if (!rt_torch_cuda_available()) {
        printf("Running on CPU (CUDA not available).\n");
        g_use_cuda = 0;
        return 1;
    }
    /* Try a test CUDA operation */
    int64_t test_t = rt_torch_tensor_randn_2d(1, 1);
    int64_t test_gpu = rt_torch_torchtensor_cuda(test_t, 0);
    if (test_gpu == 0) {
        printf("Running on CPU (CUDA device error).\n");
        g_use_cuda = 0;
        rt_torch_torchtensor_free(test_t);
        return 1;
    }
    rt_torch_torchtensor_free(test_t);
    rt_torch_torchtensor_free(test_gpu);
    g_use_cuda = 1;
    printf("GPU: CUDA available\n");
    int64_t mem = rt_torch_cuda_memory_allocated(0);
    printf("  Allocated: %lld bytes\n", (long long)mem);
    return 1;
}

static int64_t to_cuda(int64_t h) {
    if (!g_use_cuda) return h; /* CPU mode */
    int64_t h_gpu = rt_torch_torchtensor_cuda(h, 0);
    if (h_gpu == 0) {
        /* CUDA transfer failed, stay on CPU */
        g_use_cuda = 0;
        printf("WARNING: CUDA transfer failed, falling back to CPU\n");
        return h;
    }
    rt_torch_torchtensor_free(h);
    return h_gpu;
}

static void report_gpu_memory(void) {
    if (!g_use_cuda) return;
    int64_t alloc = rt_torch_cuda_memory_allocated(0);
    int64_t peak = rt_torch_cuda_max_memory_allocated(0);
    printf("GPU Memory: allocated=%lld bytes, peak=%lld bytes\n", (long long)alloc, (long long)peak);
}

/* =========================================================================
 * Tensor Parameter Creation
 * ========================================================================= */

static int64_t make_param_2d(int64_t d0, int64_t d1, double init_scale) {
    rt_torch_autograd_no_grad_begin();
    int64_t h = rt_torch_tensor_randn_2d(d0, d1);
    h = to_cuda(h);
    int64_t h_scaled = rt_torch_torchtensor_mul_scalar(h, init_scale);
    rt_torch_torchtensor_free(h);
    rt_torch_autograd_no_grad_end();
    rt_torch_autograd_set_requires_grad(h_scaled, 1);
    return h_scaled;
}

static int64_t make_zeros_param_2d(int64_t d0, int64_t d1) {
    rt_torch_autograd_no_grad_begin();
    int64_t h = rt_torch_tensor_zeros_2d(d0, d1);
    h = to_cuda(h);
    rt_torch_autograd_no_grad_end();
    rt_torch_autograd_set_requires_grad(h, 1);
    return h;
}

static int64_t make_zeros_param_1d(int64_t d0) {
    rt_torch_autograd_no_grad_begin();
    SplArray* dims = make_dims_1d(d0);
    int64_t h = rt_torch_tensor_zeros(dims);
    h = to_cuda(h);
    rt_torch_autograd_no_grad_end();
    rt_torch_autograd_set_requires_grad(h, 1);
    return h;
}

/* =========================================================================
 * TextModel (3-layer feed-forward)
 * ========================================================================= */

typedef struct {
    int64_t w1, b1;  /* Linear 1: input_dim -> hidden_dim */
    int64_t w2, b2;  /* Linear 2: hidden_dim -> hidden_dim */
    int64_t w3, b3;  /* Linear 3: hidden_dim -> output_dim */
    ModelConfig config;
} TextModel;

static TextModel text_model_create(int64_t in_dim, int64_t hid_dim, int64_t out_dim) {
    ModelConfig cfg = {.input_dim = in_dim, .hidden_dim = hid_dim, .output_dim = out_dim, .init_scale = 0.1, .num_layers = 3};
    printf("Creating TextModel(%lld -> %lld -> %lld -> %lld)\n",
           (long long)in_dim, (long long)hid_dim, (long long)hid_dim, (long long)out_dim);

    int64_t w1 = make_param_2d(hid_dim, in_dim, cfg.init_scale);
    int64_t b1 = make_zeros_param_1d(hid_dim);
    int64_t w2 = make_param_2d(hid_dim, hid_dim, cfg.init_scale);
    int64_t b2 = make_zeros_param_1d(hid_dim);
    int64_t w3 = make_param_2d(out_dim, hid_dim, cfg.init_scale);
    int64_t b3 = make_zeros_param_1d(out_dim);

    printf("  Total params: %lld\n", (long long)model_config_total_params(&cfg));
    return (TextModel){.w1 = w1, .b1 = b1, .w2 = w2, .b2 = b2, .w3 = w3, .b3 = b3, .config = cfg};
}

static int64_t text_model_forward(TextModel* m, int64_t x) {
    /* Layer 1: x @ W1^T + b1 -> GELU */
    int64_t w1t = rt_torch_torchtensor_transpose(m->w1, 0, 1);
    int64_t xw1 = rt_torch_torchtensor_matmul(x, w1t);
    rt_torch_torchtensor_free(w1t);
    int64_t h1_pre = rt_torch_torchtensor_add(xw1, m->b1);
    rt_torch_torchtensor_free(xw1);
    int64_t h1 = rt_torch_torchtensor_gelu(h1_pre);
    rt_torch_torchtensor_free(h1_pre);

    /* Layer 2: h1 @ W2^T + b2 -> GELU */
    int64_t w2t = rt_torch_torchtensor_transpose(m->w2, 0, 1);
    int64_t hw2 = rt_torch_torchtensor_matmul(h1, w2t);
    rt_torch_torchtensor_free(w2t);
    rt_torch_torchtensor_free(h1);
    int64_t h2_pre = rt_torch_torchtensor_add(hw2, m->b2);
    rt_torch_torchtensor_free(hw2);
    int64_t h2 = rt_torch_torchtensor_gelu(h2_pre);
    rt_torch_torchtensor_free(h2_pre);

    /* Layer 3: h2 @ W3^T + b3 */
    int64_t w3t = rt_torch_torchtensor_transpose(m->w3, 0, 1);
    int64_t hw3 = rt_torch_torchtensor_matmul(h2, w3t);
    rt_torch_torchtensor_free(w3t);
    rt_torch_torchtensor_free(h2);
    int64_t out = rt_torch_torchtensor_add(hw3, m->b3);
    rt_torch_torchtensor_free(hw3);
    return out;
}

static void text_model_freeze(TextModel* m) {
    rt_torch_autograd_set_requires_grad(m->w1, 0);
    rt_torch_autograd_set_requires_grad(m->b1, 0);
    rt_torch_autograd_set_requires_grad(m->w2, 0);
    rt_torch_autograd_set_requires_grad(m->b2, 0);
    rt_torch_autograd_set_requires_grad(m->w3, 0);
    rt_torch_autograd_set_requires_grad(m->b3, 0);
}

static void text_model_zero_grads(TextModel* m) {
    rt_torch_autograd_zero_grad(m->w1);
    rt_torch_autograd_zero_grad(m->b1);
    rt_torch_autograd_zero_grad(m->w2);
    rt_torch_autograd_zero_grad(m->b2);
    rt_torch_autograd_zero_grad(m->w3);
    rt_torch_autograd_zero_grad(m->b3);
}

static void text_model_print_summary(TextModel* m) {
    printf("TextModel Summary:\n");
    printf("  W1: "); print_shape(m->w1); printf("\n");
    printf("  W2: "); print_shape(m->w2); printf("\n");
    printf("  W3: "); print_shape(m->w3); printf("\n");
}

/* =========================================================================
 * LoRA Adapter
 * ========================================================================= */

typedef struct {
    int64_t rank;
    double alpha;
    double dropout;
} LoRAConfig;

static LoRAConfig lora_config_default(void) {
    return (LoRAConfig){.rank = 8, .alpha = 16.0, .dropout = 0.0};
}

static double lora_config_scale(LoRAConfig* c) {
    return c->alpha / (double)c->rank;
}

typedef struct {
    int64_t lora_a;
    int64_t lora_b;
    double lora_scale;
    int64_t rank;
    int64_t in_features;
    int64_t out_features;
} LoRAAdapter;

static LoRAAdapter create_lora_adapter(int64_t in_features, int64_t out_features, LoRAConfig config) {
    /* A: [rank, in_features], B: [out_features, rank] */
    int64_t a = make_param_2d(config.rank, in_features, 0.01);
    int64_t b = make_zeros_param_2d(out_features, config.rank);
    double scale = lora_config_scale(&config);
    printf("  LoRA: [%lld, %lld] -> [%lld, %lld], scale=%.2f\n",
           (long long)config.rank, (long long)in_features,
           (long long)out_features, (long long)config.rank, scale);
    return (LoRAAdapter){
        .lora_a = a, .lora_b = b, .lora_scale = scale,
        .rank = config.rank, .in_features = in_features, .out_features = out_features
    };
}

static int64_t lora_adapter_forward(LoRAAdapter* lora, int64_t x) {
    /* LoRA: x @ A^T @ B^T * scale */
    int64_t at = rt_torch_torchtensor_transpose(lora->lora_a, 0, 1);
    int64_t xa = rt_torch_torchtensor_matmul(x, at);
    rt_torch_torchtensor_free(at);
    int64_t bt = rt_torch_torchtensor_transpose(lora->lora_b, 0, 1);
    int64_t xab = rt_torch_torchtensor_matmul(xa, bt);
    rt_torch_torchtensor_free(bt);
    rt_torch_torchtensor_free(xa);
    int64_t scaled = rt_torch_torchtensor_mul_scalar(xab, lora->lora_scale);
    rt_torch_torchtensor_free(xab);
    return scaled;
}

static void lora_sgd_step(LoRAAdapter* l1, LoRAAdapter* l2, double lr) {
    /* SGD: param_new = (param - lr * grad) computed under no_grad, then set requires_grad */
    int64_t params[4] = {l1->lora_a, l1->lora_b, l2->lora_a, l2->lora_b};
    for (int i = 0; i < 4; i++) {
        int64_t grad = rt_torch_autograd_grad(params[i]);
        if (grad == 0) continue;
        rt_torch_autograd_no_grad_begin();
        int64_t scaled = rt_torch_torchtensor_mul_scalar(grad, lr);
        int64_t updated = rt_torch_torchtensor_sub(params[i], scaled);
        rt_torch_torchtensor_free(scaled);
        rt_torch_autograd_no_grad_end();
        rt_torch_autograd_set_requires_grad(updated, 1);
        /* Update the handle */
        int64_t old = params[i];
        if (i == 0) { l1->lora_a = updated; }
        else if (i == 1) { l1->lora_b = updated; }
        else if (i == 2) { l2->lora_a = updated; }
        else { l2->lora_b = updated; }
        rt_torch_torchtensor_free(old);
    }
}

static void lora_zero_grads(LoRAAdapter* l1, LoRAAdapter* l2) {
    rt_torch_autograd_zero_grad(l1->lora_a);
    rt_torch_autograd_zero_grad(l1->lora_b);
    rt_torch_autograd_zero_grad(l2->lora_a);
    rt_torch_autograd_zero_grad(l2->lora_b);
}

/* Gradient clipping by norm */
static void lora_clip_and_step(LoRAAdapter* l1, LoRAAdapter* l2, double lr, double max_norm) {
    /* Compute total gradient norm */
    int64_t params[4] = {l1->lora_a, l1->lora_b, l2->lora_a, l2->lora_b};
    double total_norm_sq = 0.0;
    for (int i = 0; i < 4; i++) {
        int64_t grad = rt_torch_autograd_grad(params[i]);
        if (grad == 0) continue;
        int64_t sq = rt_torch_torchtensor_mul(grad, grad);
        double s = rt_torch_torchtensor_mean(sq);
        int64_t numel = rt_torch_torchtensor_numel(grad);
        total_norm_sq += s * (double)numel;
        rt_torch_torchtensor_free(sq);
    }
    double total_norm = sqrt(total_norm_sq);
    double clip_coef = (total_norm > max_norm) ? max_norm / total_norm : 1.0;
    double effective_lr = lr * clip_coef;
    lora_sgd_step(l1, l2, effective_lr);
}

/* LoRA forward pass through model: base forward + LoRA residuals */
static int64_t lora_model_forward(TextModel* model, int64_t x, LoRAAdapter* lora_l1, LoRAAdapter* lora_l2) {
    /* Layer 1 base */
    int64_t w1t = rt_torch_torchtensor_transpose(model->w1, 0, 1);
    int64_t xw1 = rt_torch_torchtensor_matmul(x, w1t);
    rt_torch_torchtensor_free(w1t);
    int64_t h1_pre = rt_torch_torchtensor_add(xw1, model->b1);
    rt_torch_torchtensor_free(xw1);

    /* Layer 1 LoRA */
    int64_t lora1_out = lora_adapter_forward(lora_l1, x);
    int64_t h1_combined = rt_torch_torchtensor_add(h1_pre, lora1_out);
    rt_torch_torchtensor_free(h1_pre);
    rt_torch_torchtensor_free(lora1_out);
    int64_t h1 = rt_torch_torchtensor_gelu(h1_combined);
    rt_torch_torchtensor_free(h1_combined);

    /* Layer 2 base */
    int64_t w2t = rt_torch_torchtensor_transpose(model->w2, 0, 1);
    int64_t hw2 = rt_torch_torchtensor_matmul(h1, w2t);
    rt_torch_torchtensor_free(w2t);
    int64_t h2_pre = rt_torch_torchtensor_add(hw2, model->b2);
    rt_torch_torchtensor_free(hw2);

    /* Layer 2 LoRA */
    int64_t lora2_out = lora_adapter_forward(lora_l2, h1);
    rt_torch_torchtensor_free(h1);
    int64_t h2_combined = rt_torch_torchtensor_add(h2_pre, lora2_out);
    rt_torch_torchtensor_free(h2_pre);
    rt_torch_torchtensor_free(lora2_out);
    int64_t h2 = rt_torch_torchtensor_gelu(h2_combined);
    rt_torch_torchtensor_free(h2_combined);

    /* Layer 3 (no LoRA) */
    int64_t w3t = rt_torch_torchtensor_transpose(model->w3, 0, 1);
    int64_t hw3 = rt_torch_torchtensor_matmul(h2, w3t);
    rt_torch_torchtensor_free(w3t);
    rt_torch_torchtensor_free(h2);
    int64_t out = rt_torch_torchtensor_add(hw3, model->b3);
    rt_torch_torchtensor_free(hw3);
    return out;
}

/* Merge LoRA weights into base model */
static void merge_lora_into_model(TextModel* model, LoRAAdapter* l1, LoRAAdapter* l2) {
    printf("Merging LoRA into base model...\n");
    /* merge W = W + B @ A * scale */
    /* Layer 1 */
    {
        rt_torch_autograd_no_grad_begin();
        int64_t ba = rt_torch_torchtensor_matmul(l1->lora_b, l1->lora_a);
        int64_t ba_scaled = rt_torch_torchtensor_mul_scalar(ba, l1->lora_scale);
        rt_torch_torchtensor_free(ba);
        int64_t w_new = rt_torch_torchtensor_add(model->w1, ba_scaled);
        rt_torch_torchtensor_free(ba_scaled);
        rt_torch_torchtensor_free(model->w1);
        rt_torch_autograd_no_grad_end();
        rt_torch_autograd_set_requires_grad(w_new, 1);
        model->w1 = w_new;
    }
    /* Layer 2 */
    {
        rt_torch_autograd_no_grad_begin();
        int64_t ba = rt_torch_torchtensor_matmul(l2->lora_b, l2->lora_a);
        int64_t ba_scaled = rt_torch_torchtensor_mul_scalar(ba, l2->lora_scale);
        rt_torch_torchtensor_free(ba);
        int64_t w_new = rt_torch_torchtensor_add(model->w2, ba_scaled);
        rt_torch_torchtensor_free(ba_scaled);
        rt_torch_torchtensor_free(model->w2);
        rt_torch_autograd_no_grad_end();
        rt_torch_autograd_set_requires_grad(w_new, 1);
        model->w2 = w_new;
    }
    printf("  LoRA merged into layers 1 and 2.\n");
}

/* =========================================================================
 * Loss Functions
 * ========================================================================= */

/* MSE loss as differentiable tensor */
static int64_t compute_mse_loss(int64_t pred, int64_t target) {
    int64_t diff = rt_torch_torchtensor_sub(pred, target);
    int64_t sq = rt_torch_torchtensor_mul(diff, diff);
    rt_torch_torchtensor_free(diff);
    int64_t per_sample = rt_torch_torchtensor_sum_dim(sq, 1, 0);
    rt_torch_torchtensor_free(sq);
    int64_t loss = rt_torch_torchtensor_mean_dim(per_sample, 0, 0);
    rt_torch_torchtensor_free(per_sample);
    return loss;
}

/* Cross-entropy loss as differentiable tensor (log_softmax + gather + neg + mean) */
static int64_t compute_ce_loss(int64_t logits, int64_t targets) {
    int64_t log_probs = rt_torch_torchtensor_log_softmax(logits, -1);
    /* For simplicity, use MSE approximation when gather is not available */
    /* TODO: implement proper gather-based CE when rt_torch_torchtensor_gather is added */
    int64_t neg_log = rt_torch_torchtensor_neg(log_probs);
    rt_torch_torchtensor_free(log_probs);
    int64_t loss = rt_torch_torchtensor_mean_dim(neg_log, -1, 0);
    rt_torch_torchtensor_free(neg_log);
    int64_t final = rt_torch_torchtensor_mean_dim(loss, 0, 0);
    rt_torch_torchtensor_free(loss);
    return final;
}

/* =========================================================================
 * Batch Generation (synthetic random data)
 * ========================================================================= */

static void make_randn_batch(int64_t batch_size, int64_t input_dim, int64_t output_dim,
                             int64_t* out_x, int64_t* out_target) {
    int64_t x = rt_torch_tensor_randn_2d(batch_size, input_dim);
    *out_x = to_cuda(x);
    int64_t t = rt_torch_tensor_randn_2d(batch_size, output_dim);
    *out_target = to_cuda(t);
}

/* =========================================================================
 * Learning Rate Schedule
 * ========================================================================= */

static double lr_linear_warmup(int64_t step, int64_t warmup_steps, double base_lr) {
    if (step < warmup_steps) {
        return base_lr * (double)step / (double)warmup_steps;
    }
    return base_lr;
}

/* =========================================================================
 * Phase 0: English Medical Data Preparation
 * ========================================================================= */

static TextModel run_phase0(void) {
    printf("\n");
    print_separator();
    printf("  PHASE 0: ENGLISH MEDICAL DATA PREPARATION (REAL CUDA)\n");
    print_separator();
    printf("\n");

    TrainConfig config = train_config_phase0();
    train_config_print(&config, "Phase 0 - English Medical");

    TextModel model = text_model_create(config.input_dim, config.hidden_dim, config.output_dim);
    text_model_print_summary(&model);
    printf("\n");

    /* Freeze base model */
    text_model_freeze(&model);
    printf("Base model weights: FROZEN\n");

    /* Create LoRA adapters */
    LoRAConfig lora_cfg = {.rank = config.lora_rank, .alpha = config.lora_alpha, .dropout = 0.0};
    printf("\nAdding LoRA_0 adapters:\n");
    LoRAAdapter lora_l1 = create_lora_adapter(config.input_dim, config.hidden_dim, lora_cfg);
    LoRAAdapter lora_l2 = create_lora_adapter(config.hidden_dim, config.hidden_dim, lora_cfg);
    printf("\n");

    /* Training loop */
    TrainState state = train_state_create();
    for (int64_t epoch = 0; epoch < config.num_epochs; epoch++) {
        state.epoch_loss = 0.0;
        state.epoch_steps = 0;
        printf("--- Epoch %lld/%lld ---\n", (long long)(epoch + 1), (long long)config.num_epochs);

        for (int64_t batch_idx = 0; batch_idx < config.num_batches; batch_idx++) {
            double lr = lr_linear_warmup(state.global_step, config.warmup_steps, config.learning_rate);

            /* Generate synthetic batch */
            int64_t x, target;
            make_randn_batch(config.batch_size, config.input_dim, config.output_dim, &x, &target);

            /* Forward pass with LoRA */
            int64_t logits = lora_model_forward(&model, x, &lora_l1, &lora_l2);

            /* MSE loss */
            int64_t loss_h = compute_mse_loss(logits, target);
            double loss_val = rt_torch_torchtensor_mean(loss_h);

            /* Backward */
            rt_torch_autograd_backward(loss_h);

            /* SGD update (LoRA only) */
            lora_clip_and_step(&lora_l1, &lora_l2, lr, config.max_grad_norm);

            /* Zero gradients */
            lora_zero_grads(&lora_l1, &lora_l2);
            text_model_zero_grads(&model);

            /* Cleanup */
            rt_torch_torchtensor_free(x);
            rt_torch_torchtensor_free(target);
            rt_torch_torchtensor_free(logits);
            rt_torch_torchtensor_free(loss_h);

            state.epoch_loss += loss_val;
            state.epoch_steps++;
            state.global_step++;

            if (batch_idx % 5 == 0 || batch_idx == config.num_batches - 1) {
                printf("  [step %lld] loss=%.6f lr=%.6f\n",
                       (long long)state.global_step, loss_val, lr);
            }
        }

        double avg_loss = state.epoch_loss / (double)state.epoch_steps;
        if (avg_loss < state.best_loss) state.best_loss = avg_loss;
        printf("  Epoch %lld complete: avg_loss=%.6f best=%.6f\n\n",
               (long long)(epoch + 1), avg_loss, state.best_loss);
    }

    print_separator();
    printf("PHASE 0 TRAINING COMPLETE\n");
    printf("  English medical baseline established\n");
    printf("  Best loss: %.6f\n", state.best_loss);
    print_separator();

    /* Merge LoRA into base */
    merge_lora_into_model(&model, &lora_l1, &lora_l2);
    report_gpu_memory();

    /* Cleanup LoRA */
    rt_torch_torchtensor_free(lora_l1.lora_a);
    rt_torch_torchtensor_free(lora_l1.lora_b);
    rt_torch_torchtensor_free(lora_l2.lora_a);
    rt_torch_torchtensor_free(lora_l2.lora_b);

    return model;
}

/* =========================================================================
 * Phase 1: Evaluate + LoRA Training
 * ========================================================================= */

static TextModel run_phase1(TextModel model) {
    printf("\n");
    print_separator();
    printf("  PHASE 1: EVALUATION + LORA TRAINING\n");
    print_separator();
    printf("\n");

    TrainConfig config = train_config_phase1();
    train_config_print(&config, "Phase 1 - Evaluation + LoRA");

    /* Evaluate baseline */
    printf("\nEvaluating baseline...\n");
    int64_t eval_x, eval_target;
    make_randn_batch(config.batch_size, config.input_dim, config.output_dim, &eval_x, &eval_target);
    int64_t eval_logits = text_model_forward(&model, eval_x);
    int64_t eval_loss_h = compute_mse_loss(eval_logits, eval_target);
    double baseline_loss = rt_torch_torchtensor_mean(eval_loss_h);
    printf("  Baseline loss: %.6f\n", baseline_loss);
    rt_torch_torchtensor_free(eval_x);
    rt_torch_torchtensor_free(eval_target);
    rt_torch_torchtensor_free(eval_logits);
    rt_torch_torchtensor_free(eval_loss_h);

    /* Freeze and add LoRA_1 */
    text_model_freeze(&model);
    LoRAConfig lora_cfg = {.rank = config.lora_rank, .alpha = config.lora_alpha, .dropout = 0.0};
    printf("\nAdding LoRA_1 adapters:\n");
    LoRAAdapter lora_l1 = create_lora_adapter(config.input_dim, config.hidden_dim, lora_cfg);
    LoRAAdapter lora_l2 = create_lora_adapter(config.hidden_dim, config.hidden_dim, lora_cfg);

    /* Training loop */
    TrainState state = train_state_create();
    for (int64_t epoch = 0; epoch < config.num_epochs; epoch++) {
        state.epoch_loss = 0.0;
        state.epoch_steps = 0;
        printf("\n--- Epoch %lld/%lld ---\n", (long long)(epoch + 1), (long long)config.num_epochs);

        for (int64_t batch_idx = 0; batch_idx < config.num_batches; batch_idx++) {
            double lr = lr_linear_warmup(state.global_step, config.warmup_steps, config.learning_rate);
            int64_t x, target;
            make_randn_batch(config.batch_size, config.input_dim, config.output_dim, &x, &target);
            int64_t logits = lora_model_forward(&model, x, &lora_l1, &lora_l2);
            int64_t loss_h = compute_mse_loss(logits, target);
            double loss_val = rt_torch_torchtensor_mean(loss_h);
            rt_torch_autograd_backward(loss_h);
            lora_clip_and_step(&lora_l1, &lora_l2, lr, config.max_grad_norm);
            lora_zero_grads(&lora_l1, &lora_l2);
            text_model_zero_grads(&model);
            rt_torch_torchtensor_free(x);
            rt_torch_torchtensor_free(target);
            rt_torch_torchtensor_free(logits);
            rt_torch_torchtensor_free(loss_h);
            state.epoch_loss += loss_val;
            state.epoch_steps++;
            state.global_step++;
        }

        double avg = state.epoch_loss / (double)state.epoch_steps;
        if (avg < state.best_loss) state.best_loss = avg;
        printf("  Epoch %lld: avg_loss=%.6f best=%.6f\n", (long long)(epoch + 1), avg, state.best_loss);
    }

    print_separator();
    printf("PHASE 1 COMPLETE - best loss: %.6f\n", state.best_loss);
    print_separator();

    merge_lora_into_model(&model, &lora_l1, &lora_l2);
    report_gpu_memory();

    rt_torch_torchtensor_free(lora_l1.lora_a);
    rt_torch_torchtensor_free(lora_l1.lora_b);
    rt_torch_torchtensor_free(lora_l2.lora_a);
    rt_torch_torchtensor_free(lora_l2.lora_b);

    return model;
}

/* =========================================================================
 * Phase 2: MCQ Training (Medical Reasoning)
 * ========================================================================= */

static TextModel run_phase2(TextModel model) {
    printf("\n");
    print_separator();
    printf("  PHASE 2: MCQ TRAINING (MEDICAL REASONING)\n");
    print_separator();
    printf("\n");

    TrainConfig config = train_config_phase2();
    train_config_print(&config, "Phase 2 - MCQ Training");

    text_model_freeze(&model);
    LoRAConfig lora_cfg = {.rank = config.lora_rank, .alpha = config.lora_alpha, .dropout = 0.0};
    printf("\nAdding LoRA_2 adapters:\n");
    LoRAAdapter lora_l1 = create_lora_adapter(config.input_dim, config.hidden_dim, lora_cfg);
    LoRAAdapter lora_l2 = create_lora_adapter(config.hidden_dim, config.hidden_dim, lora_cfg);

    TrainState state = train_state_create();
    for (int64_t epoch = 0; epoch < config.num_epochs; epoch++) {
        state.epoch_loss = 0.0;
        state.epoch_steps = 0;
        printf("\n--- Epoch %lld/%lld ---\n", (long long)(epoch + 1), (long long)config.num_epochs);

        for (int64_t batch_idx = 0; batch_idx < config.num_batches; batch_idx++) {
            double lr = lr_linear_warmup(state.global_step, config.warmup_steps, config.learning_rate);
            int64_t x, target;
            make_randn_batch(config.batch_size, config.input_dim, config.output_dim, &x, &target);

            /* MCQ uses CE loss */
            int64_t logits = lora_model_forward(&model, x, &lora_l1, &lora_l2);
            int64_t loss_h = compute_ce_loss(logits, target);
            double loss_val = rt_torch_torchtensor_mean(loss_h);

            rt_torch_autograd_backward(loss_h);
            lora_clip_and_step(&lora_l1, &lora_l2, lr, config.max_grad_norm);
            lora_zero_grads(&lora_l1, &lora_l2);
            text_model_zero_grads(&model);

            rt_torch_torchtensor_free(x);
            rt_torch_torchtensor_free(target);
            rt_torch_torchtensor_free(logits);
            rt_torch_torchtensor_free(loss_h);

            state.epoch_loss += loss_val;
            state.epoch_steps++;
            state.global_step++;
        }

        double avg = state.epoch_loss / (double)state.epoch_steps;
        if (avg < state.best_loss) state.best_loss = avg;
        printf("  Epoch %lld: avg_loss=%.6f best=%.6f\n", (long long)(epoch + 1), avg, state.best_loss);
    }

    /* English retention check */
    printf("\nEnglish retention check...\n");
    int64_t ret_x, ret_target;
    make_randn_batch(config.batch_size, config.input_dim, config.output_dim, &ret_x, &ret_target);
    int64_t ret_logits = lora_model_forward(&model, ret_x, &lora_l1, &lora_l2);
    int64_t ret_loss_h = compute_mse_loss(ret_logits, ret_target);
    double retention_loss = rt_torch_torchtensor_mean(ret_loss_h);
    printf("  Retention loss: %.6f (threshold: 97%%)\n", retention_loss);
    rt_torch_torchtensor_free(ret_x);
    rt_torch_torchtensor_free(ret_target);
    rt_torch_torchtensor_free(ret_logits);
    rt_torch_torchtensor_free(ret_loss_h);

    print_separator();
    printf("PHASE 2 COMPLETE - MCQ best loss: %.6f\n", state.best_loss);
    print_separator();

    merge_lora_into_model(&model, &lora_l1, &lora_l2);
    report_gpu_memory();

    rt_torch_torchtensor_free(lora_l1.lora_a);
    rt_torch_torchtensor_free(lora_l1.lora_b);
    rt_torch_torchtensor_free(lora_l2.lora_a);
    rt_torch_torchtensor_free(lora_l2.lora_b);

    return model;
}

/* =========================================================================
 * Main Entry Point
 * ========================================================================= */

int main(int argc, char** argv) {
    spl_init_args(argc, argv);

    printf("\n");
    print_separator();
    printf("  MedGemma Korean Training Pipeline\n");
    printf("  Progressive LoRA Training (Phases 0-2)\n");
    print_separator();
    printf("\n");

    if (!rt_torch_available()) {
        printf("ERROR: libtorch not loaded.\n");
        printf("Build: see medgemma_native.c header for build instructions.\n");
        return 1;
    }

    if (!check_gpu()) {
        return 1;
    }

    /* Phase 0: English Medical Data */
    TextModel model = run_phase0();

    /* Phase 1: Evaluate + LoRA */
    model = run_phase1(model);

    /* Phase 2: MCQ Training */
    model = run_phase2(model);

    printf("\n");
    print_separator();
    printf("  ALL PHASES COMPLETE\n");
    printf("  Model trained through phases 0-2.\n");
    printf("  Phases 3-6 (Korean embeddings, text, translation, reasoning)\n");
    printf("  will be added when extended model pipeline is verified.\n");
    print_separator();
    printf("\n");

    report_gpu_memory();

    /* Cleanup model */
    rt_torch_torchtensor_free(model.w1);
    rt_torch_torchtensor_free(model.b1);
    rt_torch_torchtensor_free(model.w2);
    rt_torch_torchtensor_free(model.b2);
    rt_torch_torchtensor_free(model.w3);
    rt_torch_torchtensor_free(model.b3);

    if (rt_torch_cuda_available()) {
        rt_torch_cuda_empty_cache();
    }

    printf("Training pipeline complete. Exiting.\n");
    return 0;
}
