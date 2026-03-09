#include <gtest/gtest.h>
#include <cstdlib>
#include "io/cuda_io_host_mem.h"

// Test cudaHostAlloc and cudaFreeHost
TEST(CUDAHostMem, AllocAndFree){
  void* p = nullptr;
  int ok = cuda_host_alloc(&p, 64*1024);
  if (ok != 0) GTEST_SKIP() << "cudaHostAlloc failed (no CUDA runtime?)";
  EXPECT_NE(p, nullptr);
  // Memory from cudaHostAlloc is already pinned, don't try to register it again
  EXPECT_EQ(cuda_host_free(p), 0);
}

// Test cudaHostRegister on malloc'd memory
TEST(CUDAHostMem, RegisterAndUnregister){
  void* p = malloc(64*1024);
  ASSERT_NE(p, nullptr) << "malloc failed";

  // Register malloc'd memory with CUDA
  int ok = cuda_host_register(p, 64*1024);
  if (ok != 0) {
    free(p);
    GTEST_SKIP() << "cudaHostRegister failed (no CUDA runtime or insufficient permissions?)";
  }

  // Unregister and free
  EXPECT_EQ(cuda_host_unregister(p), 0);
  free(p);
}
