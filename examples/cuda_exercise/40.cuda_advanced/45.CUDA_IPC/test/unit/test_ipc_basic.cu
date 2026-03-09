// test_ipc_basic.cu - Basic tests for CUDA IPC primitives

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"
#include "common/ipc_common.h"
#include "kernels/ipc_kernel.cu"

class IPCBasicTest : public GpuTest {};

TEST_F(IPCBasicTest, CreateIPCMemoryWorks) {
    IPCMemoryHandle ipcMem;
    const size_t size = 1024 * sizeof(float);

    ASSERT_TRUE(createIPCMemory(&ipcMem, size));
    EXPECT_NE(getIPCDevicePointer(&ipcMem), nullptr);

    closeIPCMemory(&ipcMem);
}

TEST_F(IPCBasicTest, GetIPCHandleWorks) {
    IPCMemoryHandle ipcMem;
    const size_t size = 256 * sizeof(float);

    ASSERT_TRUE(createIPCMemory(&ipcMem, size));

    cudaIpcMemHandle_t handle;
    EXPECT_TRUE(getIPCHandle(&ipcMem, &handle));

    closeIPCMemory(&ipcMem);
}

TEST_F(IPCBasicTest, CreateIPCEventWorks) {
    IPCEventHandle ipcEvent;

    ASSERT_TRUE(createIPCEvent(&ipcEvent));
    EXPECT_NE(ipcEvent.event, nullptr);

    closeIPCEvent(&ipcEvent);
}

TEST_F(IPCBasicTest, RecordAndSynchronizeIPCEventWorks) {
    IPCEventHandle ipcEvent;
    ASSERT_TRUE(createIPCEvent(&ipcEvent));

    cudaStream_t stream;
    cudaStreamCreate(&stream);

    // Record event
    EXPECT_TRUE(recordIPCEvent(&ipcEvent, stream));

    // Synchronize
    EXPECT_TRUE(synchronizeIPCEvent(&ipcEvent));

    cudaStreamDestroy(stream);
    closeIPCEvent(&ipcEvent);
}

TEST_F(IPCBasicTest, IPCEventStreamWaitWorks) {
    IPCEventHandle ipcEvent;
    ASSERT_TRUE(createIPCEvent(&ipcEvent));

    cudaStream_t stream1, stream2;
    cudaStreamCreate(&stream1);
    cudaStreamCreate(&stream2);

    // Record on stream1
    EXPECT_TRUE(recordIPCEvent(&ipcEvent, stream1));

    // Wait on stream2
    EXPECT_TRUE(waitIPCEvent(&ipcEvent, stream2));

    cudaStreamSynchronize(stream1);
    cudaStreamSynchronize(stream2);

    cudaStreamDestroy(stream1);
    cudaStreamDestroy(stream2);
    closeIPCEvent(&ipcEvent);
}

// Note: Full multi-process IPC testing requires separate executables
// These tests verify the API works within a single process
