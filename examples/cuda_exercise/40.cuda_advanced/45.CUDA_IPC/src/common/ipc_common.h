// ipc_common.h - Common definitions for CUDA IPC

#pragma once

#include <cuda_runtime.h>

// IPC memory handle wrapper
struct IPCMemoryHandle {
    cudaIpcMemHandle_t handle;
    size_t size;
    void* devicePtr;
    bool isCreator;
};

// IPC event handle wrapper
struct IPCEventHandle {
    cudaIpcEventHandle_t handle;
    cudaEvent_t event;
    bool isCreator;
};

// IPC memory functions
bool createIPCMemory(IPCMemoryHandle* ipcHandle, size_t size);
bool openIPCMemory(IPCMemoryHandle* ipcHandle, const cudaIpcMemHandle_t* handle, size_t size);
void closeIPCMemory(IPCMemoryHandle* ipcHandle);
void* getIPCDevicePointer(const IPCMemoryHandle* ipcHandle);
bool getIPCHandle(const IPCMemoryHandle* ipcHandle, cudaIpcMemHandle_t* outHandle);

// IPC event functions
bool createIPCEvent(IPCEventHandle* ipcEvent);
bool openIPCEvent(IPCEventHandle* ipcEvent, const cudaIpcEventHandle_t* handle);
void closeIPCEvent(IPCEventHandle* ipcEvent);
bool recordIPCEvent(IPCEventHandle* ipcEvent, cudaStream_t stream);
bool waitIPCEvent(IPCEventHandle* ipcEvent, cudaStream_t stream);
bool synchronizeIPCEvent(IPCEventHandle* ipcEvent);
bool getIPCEventHandle(const IPCEventHandle* ipcEvent, cudaIpcEventHandle_t* outHandle);
