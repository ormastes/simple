// HandleTable.h - Opaque handle ↔ UObject pointer mapping
// Part of SimpleWasm Unreal bridge

#pragma once

#include "CoreMinimal.h"

/**
 * Maps opaque int32 handles (passed across the WASM boundary) to typed UObject pointers.
 * Thread-safe for single-threaded game-thread use (Unreal's standard model).
 */
template<typename T>
class HandleTable
{
public:
    /** Add an object and return its handle. */
    int32 Add(T* Obj)
    {
        int32 Handle = NextHandle++;
        Table.Add(Handle, Obj);
        return Handle;
    }

    /** Retrieve an object by handle. Returns nullptr if not found. */
    T* Get(int32 Handle) const
    {
        T* const* Found = Table.Find(Handle);
        return Found ? *Found : nullptr;
    }

    /** Remove a handle from the table. */
    void Remove(int32 Handle)
    {
        Table.Remove(Handle);
    }

    /** Check if a handle is valid. */
    bool Contains(int32 Handle) const
    {
        return Table.Contains(Handle);
    }

    /** Remove all entries. */
    void Reset()
    {
        Table.Reset();
        NextHandle = 1;
    }

    /** Number of live entries. */
    int32 Num() const
    {
        return Table.Num();
    }

private:
    TMap<int32, T*> Table;
    int32 NextHandle = 1;
};
