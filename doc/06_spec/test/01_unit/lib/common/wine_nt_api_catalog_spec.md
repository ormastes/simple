# Wine Nt Api Catalog Specification

> <details>

<!-- sdn-diagram:id=wine_nt_api_catalog_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_nt_api_catalog_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_nt_api_catalog_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_nt_api_catalog_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 46 | 46 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Nt Api Catalog Specification

## Scenarios

### Wine NT API catalog

#### keeps the executable hello surface to the implemented console/process calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_symbols_for_hello()
expect(symbols.len()).to_equal(3)
expect(symbols[0]).to_equal("GetStdHandle")
expect(wine_nt_api_import_gate("KERNEL32.dll", symbols)).to_equal("ready")
```

</details>

#### catalogs broader NT and Win32 prerequisites without marking them implemented

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val future = wine_nt_api_catalogued_future_symbols()
expect(future.len()).to_be_greater_than(30)
val entry = wine_nt_api_symbol_state("kernel32.dll", "VirtualAlloc")
expect(entry.category).to_equal("virtual-memory")
expect(entry.state).to_equal("implemented")
```

</details>

#### records modeled precondition calls and keeps non-hello symbols on dedicated gates

<details>
<summary>Executable SSpec</summary>

Runnable source: 80 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val modeled = wine_nt_api_modeled_precondition_symbols()
expect(modeled.len()).to_equal(116)
expect(modeled[0]).to_equal("VirtualAlloc")
expect(modeled[3]).to_equal("CreateFileW")
expect(modeled[5]).to_equal("GetFileType")
expect(modeled[7]).to_equal("GetFileAttributesW")
expect(modeled[9]).to_equal("GetFileInformationByHandle")
expect(modeled[10]).to_equal("SetFilePointer")
expect(modeled[11]).to_equal("DeleteFileW")
expect(modeled[113]).to_equal("LdrLoadDll")
expect(modeled[114]).to_equal("LdrGetProcedureAddress")
expect(modeled[115]).to_equal("LdrUnloadDll")
expect(modeled[12]).to_equal("CopyFileW")
expect(modeled[13]).to_equal("MoveFileW")
expect(modeled[14]).to_equal("CreateDirectoryW")
expect(modeled[15]).to_equal("RemoveDirectoryW")
expect(modeled[16]).to_equal("CreateThread")
expect(modeled[19]).to_equal("SetLastError")
expect(modeled[20]).to_equal("FormatMessageW")
expect(modeled[21]).to_equal("GetCommandLineW")
expect(modeled[23]).to_equal("GetCurrentDirectoryW")
expect(modeled[26]).to_equal("GetEnvironmentVariableW")
expect(modeled[28]).to_equal("ExpandEnvironmentStringsW")
expect(modeled[29]).to_equal("GetProcessHeap")
expect(modeled[32]).to_equal("LocalAlloc")
expect(modeled[35]).to_equal("LocalFree")
expect(modeled[36]).to_equal("GlobalAlloc")
expect(modeled[37]).to_equal("GlobalSize")
expect(modeled[38]).to_equal("GlobalLock")
expect(modeled[39]).to_equal("GlobalUnlock")
expect(modeled[40]).to_equal("GlobalReAlloc")
expect(modeled[41]).to_equal("GlobalFree")
expect(modeled[42]).to_equal("NtAllocateVirtualMemory")
expect(modeled[46]).to_equal("NtOpenFile")
expect(modeled[48]).to_equal("NtWriteFile")
expect(modeled[50]).to_equal("NtQueryInformationFile")
expect(modeled[51]).to_equal("NtQueryAttributesFile")
expect(modeled[52]).to_equal("NtQueryDirectoryFile")
expect(modeled[53]).to_equal("NtSetInformationFile")
expect(modeled[54]).to_equal("NtCreateSection")
expect(modeled[56]).to_equal("NtUnmapViewOfSection")
expect(modeled[57]).to_equal("RtlAllocateHeap")
expect(modeled[59]).to_equal("RtlInitUnicodeString")
expect(modeled[61]).to_equal("RtlFreeAnsiString")
expect(modeled[62]).to_equal("GetModuleHandleW")
expect(modeled[64]).to_equal("LoadLibraryExW")
expect(modeled[66]).to_equal("FreeLibrary")
expect(modeled[67]).to_equal("GetTickCount")
expect(modeled[71]).to_equal("GetVersionExW")
expect(modeled[72]).to_equal("GetWindowsDirectoryW")
expect(modeled[75]).to_equal("GetTempFileNameW")
expect(modeled[76]).to_equal("GetFullPathNameW")
expect(modeled[77]).to_equal("SearchPathW")
expect(modeled[78]).to_equal("GetCurrentProcessId")
expect(modeled[81]).to_equal("GetCurrentThread")
expect(modeled[82]).to_equal("CreateEventW")
expect(modeled[84]).to_equal("ResetEvent")
expect(modeled[85]).to_equal("GetStartupInfoW")
expect(modeled[86]).to_equal("InitializeCriticalSection")
expect(modeled[89]).to_equal("DeleteCriticalSection")
expect(modeled[90]).to_equal("GlobalAddAtomW")
expect(modeled[92]).to_equal("GlobalDeleteAtom")
expect(modeled[93]).to_equal("TlsAlloc")
expect(modeled[96]).to_equal("TlsFree")
expect(modeled[97]).to_equal("FlsAlloc")
expect(modeled[100]).to_equal("FlsFree")
expect(modeled[101]).to_equal("InterlockedIncrement")
expect(modeled[105]).to_equal("InterlockedExchangeAdd")
expect(modeled[106]).to_equal("NtQuerySystemInformation")
expect(modeled[107]).to_equal("NtQueryInformationProcess")
expect(modeled[108]).to_equal("NtQueryInformationThread")
expect(modeled[109]).to_equal("NtOpenDirectoryObject")
expect(modeled[110]).to_equal("NtQueryDirectoryObject")
expect(modeled[111]).to_equal("NtOpenKey")
expect(modeled[112]).to_equal("NtQueryValueKey")
expect(wine_nt_api_import_gate("kernel32.dll", ["GetStdHandle", "WriteFile", "ExitProcess", "VirtualAlloc"])).to_equal("wrong-category:VirtualAlloc")
expect(wine_nt_api_import_gate("kernel32.dll", ["GetStdHandle", "WriteFile", "ExitProcess", "CreateFileW"])).to_equal("wrong-category:CreateFileW")
expect(wine_nt_api_import_gate("kernel32.dll", ["GetStdHandle", "WriteFile", "ExitProcess", "CreateThread"])).to_equal("wrong-category:CreateThread")
expect(wine_nt_api_import_gate("kernel32.dll", ["GetStdHandle", "WriteFile", "ExitProcess", "GetCommandLineW"])).to_equal("wrong-category:GetCommandLineW")
expect(wine_nt_api_import_gate("kernel32.dll", ["GetStdHandle", "WriteFile", "ExitProcess", "HeapAlloc"])).to_equal("wrong-category:HeapAlloc")
```

</details>

#### keeps GUI and GDI catalog symbols out of the console precondition bridge

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gui = wine_nt_api_catalogued_gui_symbols()
expect(gui.len()).to_equal(12)
expect(gui[0]).to_equal("CreateWindowExW")
expect(gui[8]).to_equal("TextOutW")
```

</details>

#### keeps ntdll as catalogued but not import-ready for the hello milestone

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_nt_api_dll_gate("ntdll.dll")).to_equal("catalogued-dll:ntdll.dll")
expect(wine_nt_api_import_gate("ntdll.dll", ["NtAllocateVirtualMemory"])).to_equal("catalogued-dll:ntdll.dll")
expect(wine_nt_api_ntdll_file_io_import_gate("ntdll.dll", ["RtlAllocateHeap"])).to_equal("wrong-category:RtlAllocateHeap")
```

</details>

#### blocks unknown imports before dispatch can pretend they exist

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_nt_api_import_gate("kernel32.dll", ["GetStdHandle", "WriteFile", "ExitProcess", "UnknownApi"])).to_equal("unsupported-symbol:UnknownApi")
```

</details>

#### keeps the generic hello bridge separate from implemented dedicated KERNEL32 families

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_nt_api_import_gate("kernel32.dll", ["GetStdHandle", "WriteFile", "ExitProcess", "VirtualAlloc"])).to_equal("wrong-category:VirtualAlloc")
expect(wine_nt_api_dispatch_gate(["GetStdHandle", "WriteFile", "ExitProcess", "VirtualAlloc"])).to_equal("bridge-wrong-category:VirtualAlloc")
```

</details>

#### preserves the bridge missing-symbol order for the known hello call table

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_nt_api_dispatch_gate(["GetStdHandle"])).to_equal("bridge-missing:WriteFile")
```

</details>

#### implements bounded KERNEL32 process environment symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_kernel32_process_env_symbols()
expect(symbols.len()).to_equal(8)
expect(symbols[0]).to_equal("GetCommandLineW")
expect(symbols[2]).to_equal("GetCurrentDirectoryW")
expect(symbols[4]).to_equal("GetModuleFileNameW")
expect(symbols[7]).to_equal("ExpandEnvironmentStringsW")
expect(wine_nt_api_kernel32_process_env_import_gate("kernel32.dll", symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_process_env_dispatch_gate(symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_process_env_dispatch_gate(["GetStdHandle"])).to_equal("bridge-wrong-category:GetStdHandle")
```

</details>

#### implements bounded KERNEL32 virtual memory symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_kernel32_virtual_memory_symbols()
expect(symbols.len()).to_equal(3)
expect(symbols[0]).to_equal("VirtualAlloc")
expect(wine_nt_api_kernel32_virtual_memory_import_gate("kernel32.dll", symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_virtual_memory_dispatch_gate(symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_virtual_memory_dispatch_gate(["GetStdHandle"])).to_equal("bridge-wrong-category:GetStdHandle")
```

</details>

#### implements bounded KERNEL32 heap symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_kernel32_heap_symbols()
expect(symbols.len()).to_equal(3)
expect(symbols[0]).to_equal("GetProcessHeap")
expect(symbols[1]).to_equal("HeapAlloc")
expect(wine_nt_api_kernel32_heap_import_gate("kernel32.dll", symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_heap_dispatch_gate(symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_heap_dispatch_gate(["VirtualAlloc"])).to_equal("bridge-wrong-category:VirtualAlloc")
```

</details>

#### implements bounded KERNEL32 local-memory symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_kernel32_local_memory_symbols()
expect(symbols.len()).to_equal(4)
expect(symbols[0]).to_equal("LocalAlloc")
expect(symbols[3]).to_equal("LocalFree")
expect(wine_nt_api_kernel32_local_memory_import_gate("kernel32.dll", symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_local_memory_dispatch_gate(symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_local_memory_dispatch_gate(["HeapAlloc"])).to_equal("bridge-wrong-category:HeapAlloc")
```

</details>

#### implements bounded KERNEL32 global-memory symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_kernel32_global_memory_symbols()
expect(symbols.len()).to_equal(6)
expect(symbols[0]).to_equal("GlobalAlloc")
expect(symbols[2]).to_equal("GlobalLock")
expect(symbols[3]).to_equal("GlobalUnlock")
expect(symbols[5]).to_equal("GlobalFree")
expect(wine_nt_api_kernel32_global_memory_import_gate("kernel32.dll", symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_global_memory_dispatch_gate(symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_global_memory_dispatch_gate(["HeapAlloc"])).to_equal("bridge-wrong-category:HeapAlloc")
```

</details>

#### implements bounded KERNEL32 file I/O symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_kernel32_file_io_symbols()
expect(symbols.len()).to_equal(4)
expect(symbols[0]).to_equal("CreateFileW")
expect(symbols[2]).to_equal("GetFileType")
expect(symbols[3]).to_equal("CloseHandle")
expect(wine_nt_api_kernel32_file_io_import_gate("kernel32.dll", symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_file_io_dispatch_gate(symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_file_io_dispatch_gate(["HeapAlloc"])).to_equal("bridge-wrong-category:HeapAlloc")
```

</details>

#### implements bounded KERNEL32 file metadata symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_kernel32_file_metadata_symbols()
expect(symbols.len()).to_equal(6)
expect(symbols[0]).to_equal("GetFileAttributesW")
expect(symbols[3]).to_equal("GetFileInformationByHandle")
expect(symbols[5]).to_equal("CloseHandle")
expect(wine_nt_api_kernel32_file_metadata_import_gate("kernel32.dll", symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_file_metadata_dispatch_gate(symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_file_metadata_dispatch_gate(["HeapAlloc"])).to_equal("bridge-wrong-category:HeapAlloc")
```

</details>

#### implements bounded KERNEL32 file-management symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_kernel32_file_management_symbols()
expect(symbols.len()).to_equal(5)
expect(symbols[0]).to_equal("DeleteFileW")
expect(symbols[1]).to_equal("CopyFileW")
expect(symbols[2]).to_equal("MoveFileW")
expect(symbols[3]).to_equal("CreateDirectoryW")
expect(symbols[4]).to_equal("RemoveDirectoryW")
expect(wine_nt_api_kernel32_file_management_import_gate("kernel32.dll", symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_file_management_dispatch_gate(symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_file_management_dispatch_gate(["CloseHandle"])).to_equal("bridge-wrong-category:CloseHandle")
```

</details>

#### implements bounded KERNEL32 thread/wait symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_kernel32_thread_wait_symbols()
expect(symbols.len()).to_equal(3)
expect(symbols[0]).to_equal("CreateThread")
expect(wine_nt_api_kernel32_thread_wait_import_gate("kernel32.dll", symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_thread_wait_dispatch_gate(symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_thread_wait_dispatch_gate(["CreateFileW"])).to_equal("bridge-wrong-category:CreateFileW")
```

</details>

#### implements bounded KERNEL32 error-state symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_kernel32_error_state_symbols()
expect(symbols.len()).to_equal(3)
expect(symbols[0]).to_equal("SetLastError")
expect(symbols[2]).to_equal("FormatMessageW")
expect(wine_nt_api_kernel32_error_state_import_gate("kernel32.dll", symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_error_state_dispatch_gate(symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_error_state_dispatch_gate(["HeapAlloc"])).to_equal("bridge-wrong-category:HeapAlloc")
```

</details>

#### implements bounded KERNEL32 module loader symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_kernel32_module_loader_symbols()
expect(symbols.len()).to_equal(5)
expect(symbols[0]).to_equal("GetModuleHandleW")
expect(symbols[2]).to_equal("LoadLibraryExW")
expect(symbols[4]).to_equal("FreeLibrary")
expect(wine_nt_api_kernel32_module_loader_import_gate("kernel32.dll", symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_module_loader_dispatch_gate(symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_module_loader_dispatch_gate(["VirtualAlloc"])).to_equal("bridge-wrong-category:VirtualAlloc")
```

</details>

#### implements bounded KERNEL32 time/version symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_kernel32_time_version_symbols()
expect(symbols.len()).to_equal(5)
expect(symbols[0]).to_equal("GetTickCount")
expect(symbols[4]).to_equal("GetVersionExW")
expect(wine_nt_api_kernel32_time_version_import_gate("kernel32.dll", symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_time_version_dispatch_gate(symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_time_version_dispatch_gate(["HeapAlloc"])).to_equal("bridge-wrong-category:HeapAlloc")
```

</details>

#### implements bounded KERNEL32 path symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_kernel32_path_symbols()
expect(symbols.len()).to_equal(6)
expect(symbols[0]).to_equal("GetWindowsDirectoryW")
expect(symbols[3]).to_equal("GetTempFileNameW")
expect(symbols[4]).to_equal("GetFullPathNameW")
expect(symbols[5]).to_equal("SearchPathW")
expect(wine_nt_api_kernel32_path_import_gate("kernel32.dll", symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_path_dispatch_gate(symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_path_dispatch_gate(["HeapAlloc"])).to_equal("bridge-wrong-category:HeapAlloc")
```

</details>

#### implements bounded KERNEL32 process identity symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_kernel32_process_identity_symbols()
expect(symbols.len()).to_equal(4)
expect(symbols[0]).to_equal("GetCurrentProcessId")
expect(symbols[3]).to_equal("GetCurrentThread")
expect(wine_nt_api_kernel32_process_identity_import_gate("kernel32.dll", symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_process_identity_dispatch_gate(symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_process_identity_dispatch_gate(["HeapAlloc"])).to_equal("bridge-wrong-category:HeapAlloc")
```

</details>

#### implements bounded KERNEL32 sync event symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_kernel32_sync_event_symbols()
expect(symbols.len()).to_equal(4)
expect(symbols[0]).to_equal("CreateEventW")
expect(symbols[3]).to_equal("ResetEvent")
expect(wine_nt_api_kernel32_sync_event_import_gate("kernel32.dll", symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_sync_event_dispatch_gate(symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_sync_event_dispatch_gate(["HeapAlloc"])).to_equal("bridge-wrong-category:HeapAlloc")
```

</details>

#### implements bounded KERNEL32 startup info symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_kernel32_startup_info_symbols()
expect(symbols.len()).to_equal(2)
expect(symbols[0]).to_equal("GetStartupInfoW")
expect(symbols[1]).to_equal("GetStdHandle")
expect(wine_nt_api_kernel32_startup_info_import_gate("kernel32.dll", symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_startup_info_dispatch_gate(symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_startup_info_dispatch_gate(["HeapAlloc"])).to_equal("bridge-wrong-category:HeapAlloc")
```

</details>

#### implements bounded KERNEL32 critical-section symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_kernel32_critical_section_symbols()
expect(symbols.len()).to_equal(4)
expect(symbols[0]).to_equal("InitializeCriticalSection")
expect(symbols[3]).to_equal("DeleteCriticalSection")
expect(wine_nt_api_kernel32_critical_section_import_gate("kernel32.dll", symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_critical_section_dispatch_gate(symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_critical_section_dispatch_gate(["HeapAlloc"])).to_equal("bridge-wrong-category:HeapAlloc")
```

</details>

#### implements bounded KERNEL32 atom-table symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_kernel32_atom_table_symbols()
expect(symbols.len()).to_equal(3)
expect(symbols[0]).to_equal("GlobalAddAtomW")
expect(symbols[2]).to_equal("GlobalDeleteAtom")
expect(wine_nt_api_kernel32_atom_table_import_gate("kernel32.dll", symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_atom_table_dispatch_gate(symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_atom_table_dispatch_gate(["HeapAlloc"])).to_equal("bridge-wrong-category:HeapAlloc")
```

</details>

#### implements bounded KERNEL32 TLS symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_kernel32_tls_symbols()
expect(symbols.len()).to_equal(4)
expect(symbols[0]).to_equal("TlsAlloc")
expect(symbols[3]).to_equal("TlsFree")
expect(wine_nt_api_kernel32_tls_import_gate("kernel32.dll", symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_tls_dispatch_gate(symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_tls_dispatch_gate(["HeapAlloc"])).to_equal("bridge-wrong-category:HeapAlloc")
```

</details>

#### implements bounded KERNEL32 FLS symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_kernel32_fls_symbols()
expect(symbols.len()).to_equal(4)
expect(symbols[0]).to_equal("FlsAlloc")
expect(symbols[3]).to_equal("FlsFree")
expect(wine_nt_api_kernel32_fls_import_gate("kernel32.dll", symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_fls_dispatch_gate(symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_fls_dispatch_gate(["HeapAlloc"])).to_equal("bridge-wrong-category:HeapAlloc")
```

</details>

#### implements bounded KERNEL32 interlocked symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_kernel32_interlocked_symbols()
expect(symbols.len()).to_equal(5)
expect(symbols[0]).to_equal("InterlockedIncrement")
expect(symbols[4]).to_equal("InterlockedExchangeAdd")
expect(wine_nt_api_kernel32_interlocked_import_gate("kernel32.dll", symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_interlocked_dispatch_gate(symbols)).to_equal("ready")
expect(wine_nt_api_kernel32_interlocked_dispatch_gate(["HeapAlloc"])).to_equal("bridge-wrong-category:HeapAlloc")
```

</details>

#### implements bounded NTDLL virtual memory symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_ntdll_virtual_memory_symbols()
expect(symbols.len()).to_equal(3)
expect(symbols[0]).to_equal("NtAllocateVirtualMemory")
expect(wine_nt_api_ntdll_virtual_memory_import_gate("ntdll.dll", symbols)).to_equal("ready")
expect(wine_nt_api_ntdll_virtual_memory_dispatch_gate(symbols)).to_equal("ready")
expect(wine_nt_api_ntdll_virtual_memory_dispatch_gate(["RtlAllocateHeap"])).to_equal("bridge-wrong-category:RtlAllocateHeap")
```

</details>

#### implements bounded NTDLL file I/O symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_ntdll_file_io_symbols()
expect(symbols.len()).to_equal(9)
expect(symbols[0]).to_equal("NtCreateFile")
expect(symbols[1]).to_equal("NtOpenFile")
expect(symbols[3]).to_equal("NtWriteFile")
expect(symbols[5]).to_equal("NtQueryInformationFile")
expect(symbols[6]).to_equal("NtQueryAttributesFile")
expect(symbols[7]).to_equal("NtQueryDirectoryFile")
expect(symbols[8]).to_equal("NtSetInformationFile")
expect(wine_nt_api_ntdll_file_io_import_gate("ntdll.dll", symbols)).to_equal("ready")
expect(wine_nt_api_ntdll_file_io_dispatch_gate(symbols)).to_equal("ready")
expect(wine_nt_api_ntdll_file_io_dispatch_gate(["NtAllocateVirtualMemory"])).to_equal("bridge-wrong-category:NtAllocateVirtualMemory")
```

</details>

#### implements bounded NTDLL sync event symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_ntdll_sync_event_symbols()
expect(symbols.len()).to_equal(4)
expect(symbols[0]).to_equal("NtCreateEvent")
expect(symbols[2]).to_equal("NtWaitForSingleObject")
expect(wine_nt_api_ntdll_sync_event_import_gate("ntdll.dll", symbols)).to_equal("ready")
expect(wine_nt_api_ntdll_sync_event_dispatch_gate(symbols)).to_equal("ready")
expect(wine_nt_api_ntdll_sync_event_dispatch_gate(["NtCreateFile"])).to_equal("bridge-wrong-category:NtCreateFile")
```

</details>

#### implements bounded NTDLL section map symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_ntdll_section_map_symbols()
expect(symbols.len()).to_equal(3)
expect(symbols[0]).to_equal("NtCreateSection")
expect(symbols[2]).to_equal("NtUnmapViewOfSection")
expect(wine_nt_api_ntdll_section_map_import_gate("ntdll.dll", symbols)).to_equal("ready")
expect(wine_nt_api_ntdll_section_map_dispatch_gate(symbols)).to_equal("ready")
expect(wine_nt_api_ntdll_section_map_dispatch_gate(["NtCreateFile"])).to_equal("bridge-wrong-category:NtCreateFile")
```

</details>

#### implements bounded NTDLL system information symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_ntdll_system_info_symbols()
expect(symbols.len()).to_equal(1)
expect(symbols[0]).to_equal("NtQuerySystemInformation")
expect(wine_nt_api_ntdll_system_info_import_gate("ntdll.dll", symbols)).to_equal("ready")
expect(wine_nt_api_ntdll_system_info_dispatch_gate(symbols)).to_equal("ready")
expect(wine_nt_api_ntdll_system_info_dispatch_gate(["NtCreateFile"])).to_equal("bridge-wrong-category:NtCreateFile")
```

</details>

#### implements bounded NTDLL process information symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_ntdll_process_info_symbols()
expect(symbols.len()).to_equal(2)
expect(symbols[0]).to_equal("NtQueryInformationProcess")
expect(symbols[1]).to_equal("NtQueryInformationThread")
expect(wine_nt_api_ntdll_process_info_import_gate("ntdll.dll", symbols)).to_equal("ready")
expect(wine_nt_api_ntdll_process_info_dispatch_gate(symbols)).to_equal("ready")
expect(wine_nt_api_ntdll_process_info_dispatch_gate(["NtCreateFile"])).to_equal("bridge-wrong-category:NtCreateFile")
```

</details>

#### implements bounded NTDLL object namespace symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_ntdll_object_namespace_symbols()
expect(symbols.len()).to_equal(3)
expect(symbols[0]).to_equal("NtOpenDirectoryObject")
expect(symbols[1]).to_equal("NtQueryDirectoryObject")
expect(symbols[2]).to_equal("NtClose")
expect(wine_nt_api_ntdll_object_namespace_import_gate("ntdll.dll", symbols)).to_equal("ready")
expect(wine_nt_api_ntdll_object_namespace_dispatch_gate(symbols)).to_equal("ready")
expect(wine_nt_api_ntdll_object_namespace_dispatch_gate(["NtCreateFile"])).to_equal("bridge-wrong-category:NtCreateFile")
```

</details>

#### implements bounded NTDLL registry symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_ntdll_registry_symbols()
expect(symbols.len()).to_equal(3)
expect(symbols[0]).to_equal("NtOpenKey")
expect(symbols[1]).to_equal("NtQueryValueKey")
expect(symbols[2]).to_equal("NtClose")
expect(wine_nt_api_ntdll_registry_import_gate("ntdll.dll", symbols)).to_equal("ready")
expect(wine_nt_api_ntdll_registry_dispatch_gate(symbols)).to_equal("ready")
expect(wine_nt_api_ntdll_registry_dispatch_gate(["NtCreateFile"])).to_equal("bridge-wrong-category:NtCreateFile")
```

</details>

#### implements bounded NTDLL loader symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_ntdll_loader_symbols()
expect(symbols.len()).to_equal(3)
expect(symbols[0]).to_equal("LdrLoadDll")
expect(symbols[1]).to_equal("LdrGetProcedureAddress")
expect(symbols[2]).to_equal("LdrUnloadDll")
expect(wine_nt_api_ntdll_loader_import_gate("ntdll.dll", symbols)).to_equal("ready")
expect(wine_nt_api_ntdll_loader_dispatch_gate(symbols)).to_equal("ready")
expect(wine_nt_api_ntdll_loader_dispatch_gate(["NtCreateFile"])).to_equal("bridge-wrong-category:NtCreateFile")
```

</details>

#### implements bounded RTL heap symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_rtl_heap_symbols()
expect(symbols.len()).to_equal(2)
expect(symbols[0]).to_equal("RtlAllocateHeap")
expect(wine_nt_api_rtl_heap_import_gate("ntdll.dll", symbols)).to_equal("ready")
expect(wine_nt_api_rtl_heap_dispatch_gate(symbols)).to_equal("ready")
expect(wine_nt_api_rtl_heap_dispatch_gate(["NtCreateFile"])).to_equal("bridge-wrong-category:NtCreateFile")
```

</details>

#### implements bounded RTL string symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_rtl_string_symbols()
expect(symbols.len()).to_equal(3)
expect(symbols[0]).to_equal("RtlInitUnicodeString")
expect(symbols[2]).to_equal("RtlFreeAnsiString")
expect(wine_nt_api_rtl_string_import_gate("ntdll.dll", symbols)).to_equal("ready")
expect(wine_nt_api_rtl_string_dispatch_gate(symbols)).to_equal("ready")
expect(wine_nt_api_rtl_string_dispatch_gate(["RtlFreeHeap"])).to_equal("bridge-wrong-category:RtlFreeHeap")
```

</details>

#### implements MessageBoxW for the controlled GUI milestone

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_symbols_for_gui_hello()
expect(symbols.len()).to_equal(1)
expect(symbols[0]).to_equal("MessageBoxW")
expect(wine_nt_api_gui_import_gate("user32.dll", ["MessageBoxW"])).to_equal("ready")
expect(wine_nt_api_gui_import_gate("user32.dll", ["MessageBoxW", "TextOutW"])).to_equal("unsupported-symbol:TextOutW")
expect(wine_nt_api_gdi_import_gate("gdi32.dll", ["TextOutW"])).to_equal("ready")
expect(wine_nt_api_gui_dispatch_gate(["MessageBoxW"])).to_equal("ready")
expect(wine_nt_api_gui_dispatch_gate(["TextOutW"])).to_equal("bridge-unsupported:TextOutW")
```

</details>

#### implements the bounded USER32 window lifecycle symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_user32_window_symbols()
expect(symbols.len()).to_equal(4)
expect(symbols[0]).to_equal("CreateWindowExW")
expect(wine_nt_api_gui_import_gate("user32.dll", symbols)).to_equal("ready")
expect(wine_nt_api_gui_dispatch_gate(symbols)).to_equal("ready")
```

</details>

<details>
<summary>Advanced: implements the bounded USER32 message loop symbols</summary>

#### implements the bounded USER32 message loop symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_user32_message_symbols()
expect(symbols.len()).to_equal(4)
expect(symbols[0]).to_equal("PeekMessageW")
expect(wine_nt_api_gui_import_gate("user32.dll", symbols)).to_equal("ready")
expect(wine_nt_api_gui_dispatch_gate(symbols)).to_equal("ready")
```

</details>


</details>

#### implements the bounded GDI32 drawing symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_gdi32_drawing_symbols()
expect(symbols.len()).to_equal(4)
expect(symbols[0]).to_equal("CreateCompatibleDC")
expect(wine_nt_api_gdi_import_gate("gdi32.dll", symbols)).to_equal("ready")
expect(wine_nt_api_gdi_dispatch_gate(symbols)).to_equal("ready")
```

</details>

#### implements bounded ADVAPI32 registry symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_advapi32_registry_symbols()
expect(symbols.len()).to_equal(5)
expect(symbols[0]).to_equal("RegCreateKeyExW")
expect(wine_nt_api_advapi32_import_gate("advapi32.dll", symbols)).to_equal("ready")
expect(wine_nt_api_advapi32_dispatch_gate(symbols)).to_equal("ready")
```

</details>

#### implements bounded ADVAPI32 service-control symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = wine_nt_api_implemented_advapi32_service_symbols()
expect(symbols.len()).to_equal(5)
expect(symbols[0]).to_equal("OpenSCManagerW")
expect(wine_nt_api_advapi32_import_gate("advapi32.dll", symbols)).to_equal("ready")
expect(wine_nt_api_advapi32_dispatch_gate(symbols)).to_equal("ready")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_nt_api_catalog_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine NT API catalog

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 46 |
| Active scenarios | 46 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
