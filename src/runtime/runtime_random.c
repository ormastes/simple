#include <stdint.h>
#include <pthread.h>
#include <time.h>

#define LCG_A  UINT64_C(1664525)
#define LCG_C  UINT64_C(1013904223)
#define LCG_M  UINT64_C(4294967296)
#define LCG_M_F 4294967296.0

static uint64_t g_state      = 0;
static int      g_initialized = 0;
static pthread_mutex_t g_mutex = PTHREAD_MUTEX_INITIALIZER;

static void _init_state(void) {
    struct timespec ts;
    clock_gettime(CLOCK_REALTIME, &ts);
    uint64_t us = (uint64_t)ts.tv_sec * 1000000ULL + (uint64_t)(ts.tv_nsec / 1000);
    g_state = us % LCG_M;
    g_initialized = 1;
}

static uint64_t _advance(void) {
    g_state = (LCG_A * g_state + LCG_C) % LCG_M;
    return g_state;
}

void rt_random_seed(int64_t seed) {
    pthread_mutex_lock(&g_mutex);
    g_state = (uint64_t)seed % LCG_M;
    g_initialized = 1;
    pthread_mutex_unlock(&g_mutex);
}

int64_t rt_random_getstate(void) {
    pthread_mutex_lock(&g_mutex);
    if (!g_initialized) _init_state();
    int64_t state = (int64_t)g_state;
    pthread_mutex_unlock(&g_mutex);
    return state;
}

void rt_random_setstate(int64_t new_state) {
    pthread_mutex_lock(&g_mutex);
    g_state = (uint64_t)new_state % LCG_M;
    g_initialized = 1;
    pthread_mutex_unlock(&g_mutex);
}

int64_t rt_random_next(void) {
    pthread_mutex_lock(&g_mutex);
    if (!g_initialized) _init_state();
    int64_t val = (int64_t)_advance();
    pthread_mutex_unlock(&g_mutex);
    return val;
}

int64_t rt_random_randint(int64_t min, int64_t max) {
    if (min > max) return min;
    int64_t range = max - min + 1;
    return min + (rt_random_next() % range);
}

double rt_random_random(void) {
    return (double)rt_random_next() / LCG_M_F;
}

double rt_random_uniform(double min, double max) {
    return min + rt_random_random() * (max - min);
}
