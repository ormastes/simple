using System.Collections.Generic;
using UnityEngine;

namespace SimpleWasm
{
    /// <summary>
    /// Generic handle table mapping i32 handles to engine objects.
    /// WASM only sees opaque integer handles; the host owns the real objects.
    /// </summary>
    public class HandleTable<T> where T : class
    {
        private readonly Dictionary<int, T> _table = new Dictionary<int, T>();
        private int _nextHandle = 1; // 0 is reserved as invalid

        /// <summary>
        /// Register an object and return its integer handle.
        /// </summary>
        public int Add(T obj)
        {
            int handle = _nextHandle++;
            _table[handle] = obj;
            return handle;
        }

        /// <summary>
        /// Retrieve the object for the given handle.
        /// Returns null if the handle is invalid or has been removed.
        /// </summary>
        public T Get(int handle)
        {
            _table.TryGetValue(handle, out T obj);
            return obj;
        }

        /// <summary>
        /// Remove a handle, freeing the slot.
        /// </summary>
        public void Remove(int handle)
        {
            _table.Remove(handle);
        }

        /// <summary>
        /// Remove all handles and reset the counter.
        /// </summary>
        public void Clear()
        {
            _table.Clear();
            _nextHandle = 1;
        }

        /// <summary>
        /// Number of live handles.
        /// </summary>
        public int Count => _table.Count;
    }
}
