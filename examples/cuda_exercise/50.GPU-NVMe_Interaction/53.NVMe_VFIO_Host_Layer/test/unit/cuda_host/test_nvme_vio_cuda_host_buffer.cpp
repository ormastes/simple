#include <gtest/gtest.h>
#include <filesystem>
#include <cstdlib>
#include <cuda_runtime_api.h>
#include "io/cuda_io_host_mem.h"  // Updated from nvme_vio_cuda_host.h

static bool vfio_ok(){ return std::filesystem::exists("/dev/vfio/vfio"); }
static std::string env_or(const char* k,const char* d){ const char* v=getenv(k); return v?std::string(v):std::string(d); }

TEST(CUDAHostPinned, CreateAndDestroy){
  int ndev=0; if (cudaGetDeviceCount(&ndev)!=cudaSuccess || ndev==0) GTEST_SKIP() << "No CUDA device";
  if (!vfio_ok()) GTEST_SKIP() << "No /dev/vfio/vfio";
  auto bdf = env_or("NVME_BDF","");
  if (bdf.empty()) GTEST_SKIP() << "Set NVME_BDF";
  auto lszS = env_or("NVME_LBA_SIZE","512");
  std::uint32_t lba_sz = (std::uint32_t)std::strtoul(lszS.c_str(), nullptr, 0);
  ASSERT_NE(nvme_open(bdf.c_str(), 16, 64, lba_sz), nullptr);

  Buffer* buf = cuda_host_create_pinned_consecutive_buffer(128 * 1024);
  if (!buf) GTEST_SKIP() << "cudaHostAlloc failed or VFIO map failed";
  EXPECT_NE(buf->addr, nullptr);
  EXPECT_EQ(buf->mem_type, MemoryType::PINNED_HOST);
  EXPECT_NE(buf->iova, 0u);

  cuda_host_buffer_destroy(buf);
}
