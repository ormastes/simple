// ipc_memory.cpp - CUDA IPC memory handle management

#include <cuda_runtime.h>
#include <cstring>
#include <cstdio>

// IPC memory handle wrapper
struct IPCMemoryHandle {
    cudaIpcMemHandle_t handle;
    size_t size;
    void* devicePtr;
    bool isCreator;
};

// Create IPC-shareable device memory
bool createIPCMemory(IPCMemoryHandle* ipcHandle, size_t size) {
    if (!ipcHandle) return false;

    ipcHandle->size = size;
    ipcHandle->isCreator = true;

    // Allocate device memory
    cudaError_t err = cudaMalloc(&ipcHandle->devicePtr, size);
    if (err != cudaSuccess) {
        fprintf(stderr, "Failed to allocate device memory: %s\n", cudaGetErrorString(err));
        return false;
    }

    // Get IPC handle
    err = cudaIpcGetMemHandle(&ipcHandle->handle, ipcHandle->devicePtr);
    if (err != cudaSuccess) {
        fprintf(stderr, "Failed to get IPC handle: %s\n", cudaGetErrorString(err));
        cudaFree(ipcHandle->devicePtr);
        return false;
    }

    return true;
}

// Open IPC memory from handle
bool openIPCMemory(IPCMemoryHandle* ipcHandle, const cudaIpcMemHandle_t* handle, size_t size) {
    if (!ipcHandle || !handle) return false;

    ipcHandle->size = size;
    ipcHandle->isCreator = false;
    memcpy(&ipcHandle->handle, handle, sizeof(cudaIpcMemHandle_t));

    // Open IPC memory handle
    cudaError_t err = cudaIpcOpenMemHandle(&ipcHandle->devicePtr, *handle, cudaIpcMemLazyEnablePeerAccess);
    if (err != cudaSuccess) {
        fprintf(stderr, "Failed to open IPC handle: %s\n", cudaGetErrorString(err));
        return false;
    }

    return true;
}

// Close IPC memory
void closeIPCMemory(IPCMemoryHandle* ipcHandle) {
    if (!ipcHandle) return;

    if (ipcHandle->isCreator) {
        // Creator frees the memory
        if (ipcHandle->devicePtr) {
            cudaFree(ipcHandle->devicePtr);
            ipcHandle->devicePtr = nullptr;
        }
    } else {
        // Non-creator closes the handle
        if (ipcHandle->devicePtr) {
            cudaIpcCloseMemHandle(ipcHandle->devicePtr);
            ipcHandle->devicePtr = nullptr;
        }
    }
}

// Get device pointer from IPC handle
void* getIPCDevicePointer(const IPCMemoryHandle* ipcHandle) {
    return ipcHandle ? ipcHandle->devicePtr : nullptr;
}

// Get IPC handle for sharing
bool getIPCHandle(const IPCMemoryHandle* ipcHandle, cudaIpcMemHandle_t* outHandle) {
    if (!ipcHandle || !outHandle) return false;
    memcpy(outHandle, &ipcHandle->handle, sizeof(cudaIpcMemHandle_t));
    return true;
}
