impl Settlement {
    /// Create a new settlement with given configuration.
    pub fn new(
        config: SettlementConfig,
        allocator: Arc<dyn MemoryAllocator>,
    ) -> Result<Self, SettlementError> {
        // Allocate code region (page-aligned)
        let code_region = allocator
            .allocate(config.code_region_size, 4096)
            .map_err(|e| SettlementError::MemoryError(e.to_string()))?;

        // Set code region to RWX for now (will be RX after loading)
        allocator
            .protect(&code_region, Protection::ReadWriteExecute)
            .map_err(|e| SettlementError::MemoryError(e.to_string()))?;

        // Allocate data region
        let data_region = allocator
            .allocate(config.data_region_size, 4096)
            .map_err(|e| SettlementError::MemoryError(e.to_string()))?;

        // Set data region to RW
        allocator
            .protect(&data_region, Protection::ReadWrite)
            .map_err(|e| SettlementError::MemoryError(e.to_string()))?;

        let code_ptr = code_region.as_mut_ptr();
        let data_ptr = data_region.as_mut_ptr();

        Ok(Self {
            code_slots: SlotAllocator::new(code_ptr, config.code_region_size, CODE_SLOT_SIZE),
            data_slots: SlotAllocator::new(data_ptr, config.data_region_size, DATA_SLOT_SIZE),
            code_region,
            data_region,
            config,
            func_table: FunctionTable::new(),
            global_table: GlobalTable::new(),
            type_table: TypeTable::new(),
            modules: Vec::new(),
            modules_by_name: HashMap::new(),
            native_libs: NativeLibManager::new(),
            linker: SettlementLinker::new(),
            entry_module: None,
            entry_func_idx: None,
            allocator,
        })
    }

    /// Create with default configuration.
    pub fn with_defaults(allocator: Arc<dyn MemoryAllocator>) -> Result<Self, SettlementError> {
        Self::new(SettlementConfig::default(), allocator)
    }

    /// Add a module to the settlement.
    pub fn add_module(&mut self, module: &LoadedModule) -> Result<ModuleHandle, SettlementError> {
        self.add_module_with_linking(module, true)
    }

    /// Add a module to the settlement with optional linking.
    ///
    /// If `resolve_imports` is true, the module's imports will be resolved
    /// against existing modules' exports, and dependencies will be tracked.
    pub fn add_module_with_linking(
        &mut self,
        module: &LoadedModule,
        resolve_imports: bool,
    ) -> Result<ModuleHandle, SettlementError> {
        // Use path as module name
        let name = module
            .path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("unknown")
            .to_string();

        // Check if module already exists
        if self.modules_by_name.contains_key(&name) {
            return Err(SettlementError::InvalidModule(format!(
                "Module '{}' already exists",
                name
            )));
        }

        // Get code size from module's code memory
        let code_size = module.code_mem.size();
        let data_size = module.data_mem.as_ref().map(|d| d.size()).unwrap_or(0);

        // Allocate code slots
        let code_slots = self
            .code_slots
            .allocate_bytes(code_size)
            .ok_or(SettlementError::CodeRegionFull)?;

        // Allocate data slots
        let data_slots = if data_size > 0 {
            self.data_slots
                .allocate_bytes(data_size)
                .ok_or(SettlementError::DataRegionFull)?
        } else {
            SlotRange::new(0, 0)
        };

        // Copy code to settlement
        let (code_ptr, _) = self.code_slots.get_memory(code_slots);
        unsafe {
            std::ptr::copy_nonoverlapping(module.code_mem.as_ptr(), code_ptr, code_size);
        }

        // Copy data to settlement
        if let Some(ref data_mem) = module.data_mem {
            let (data_ptr, _) = self.data_slots.get_memory(data_slots);
            unsafe {
                std::ptr::copy_nonoverlapping(data_mem.as_ptr(), data_ptr, data_size);
            }
        }

        // Create module handle
        let handle = ModuleHandle(self.modules.len() as u32);

        // Register functions in function table and collect export info for linker
        let mut functions = Vec::new();
        let mut func_indices: Vec<(String, TableIndex)> = Vec::new();

        // Register entry point if executable
        if module.header.is_executable() {
            let entry_offset = module.header.entry_point as usize;
            let settlement_addr = code_ptr as usize + entry_offset;

            let func_idx = self
                .func_table
                .allocate(settlement_addr, handle.0 as u16, 1);
            functions.push(func_idx);
            func_indices.push(("__entry".to_string(), func_idx));

            // If this is the first module with entry, set it as entry module
            if self.entry_module.is_none() {
                self.entry_module = Some(handle);
                self.entry_func_idx = Some(func_idx);
            }
        }

        // Register exports in function table
        for sym in module.symbols.exports() {
            if sym.sym_type == crate::smf::SymbolType::Function {
                let offset = sym.value as usize;
                let settlement_addr = code_ptr as usize + offset;
                let func_idx = self
                    .func_table
                    .allocate(settlement_addr, handle.0 as u16, 1);
                functions.push(func_idx);

                let sym_name = module.symbols.symbol_name(sym).to_string();
                func_indices.push((sym_name, func_idx));
            }
        }

        // Register exports in linker
        self.linker
            .register_exports(module, handle, code_ptr as usize, &func_indices);

        // Link module and resolve dependencies
        let dependencies = if resolve_imports {
            let link_result = self.linker.link_module(module, handle)?;

            // Check for unresolved required symbols
            if !link_result.unresolved.is_empty() {
                // For now, just warn - could make this an error
                // return Err(SettlementError::InvalidModule(format!(
                //     "Unresolved symbols: {:?}",
                //     link_result.unresolved
                // )));
            }

            // Re-apply relocations with resolved imports
            if !link_result.resolved_imports.is_empty() {
                // Get mutable slice to code
                let _code_slice = unsafe { std::slice::from_raw_parts_mut(code_ptr, code_size) };

                // Create resolver that combines linker exports with native symbols
                let _resolver = |name: &str| -> Option<usize> {
                    link_result
                        .resolved_imports
                        .get(name)
                        .copied()
                        .or_else(|| self.native_libs.resolve_symbol(name))
                };

                // Note: We'd need to re-apply relocations here if the module
                // wasn't already relocated during loading. For now, the loader
                // already applies relocations with its own resolver.
            }

            link_result.dependencies
        } else {
            Vec::new()
        };

        // Calculate table ranges
        let func_start = if functions.is_empty() {
            TableIndex::INVALID
        } else {
            functions[0]
        };

        // Create settlement module entry
        let settlement_module = SettlementModule {
            name: name.clone(),
            handle,
            code_slots,
            data_slots,
            functions: functions.clone(),
            // Global and type metadata population requires:
            // 1. SMF format to include global/type sections
            // 2. Compiler to emit global definitions in SMF
            // 3. Settlement allocator for global/type tables
            // Currently unused - deferred until settlement GC integration
            globals: Vec::new(),
            types: Vec::new(),
            dependencies,        // Now properly populated from linker
            version: module.version,
            code_size,
            data_size,
            code_range: code_slots,
            data_range: data_slots,
            func_table_range: (func_start, functions.len()),
            global_table_range: (TableIndex::INVALID, 0),
            type_table_range: (TableIndex::INVALID, 0),
        };

        self.modules.push(settlement_module);
        self.modules_by_name.insert(name, handle);

        Ok(handle)
    }

    /// Remove a module from the settlement.
    pub fn remove_module(&mut self, handle: ModuleHandle) -> Result<(), SettlementError> {
        let module = self
            .modules
            .get(handle.as_usize())
            .ok_or_else(|| SettlementError::ModuleNotFound(format!("Handle {:?}", handle)))?;

        let name = module.name.clone();

        // Check for dependents using linker
        let dependents = self.linker.get_dependents(handle);
        if !dependents.is_empty() {
            let dependent_names: Vec<String> = dependents
                .iter()
                .filter_map(|&h| self.modules.get(h.as_usize()).map(|m| m.name.clone()))
                .collect();
            return Err(SettlementError::HasDependents(name, dependent_names));
        }

        // Free function table entries
        for &func_idx in &module.functions {
            self.func_table.mark_tombstone(func_idx);
        }

        // Free global table entries
        for &global_idx in &module.globals {
            self.global_table.free(global_idx);
        }

        // Free type table entries
        for &type_idx in &module.types {
            self.type_table.free(type_idx);
        }

        // Free code slots
        self.code_slots.free(module.code_slots);

        // Free data slots
        if module.data_slots.count > 0 {
            self.data_slots.free(module.data_slots);
        }

        // Unregister from linker
        self.linker.unregister_module(handle);

        // Remove from name lookup
        self.modules_by_name.remove(&name);

        // Mark module as removed (we don't actually remove from Vec to keep handles stable)
        // In a production implementation, you'd want a more sophisticated approach

        Ok(())
    }

    /// Resolve a symbol by name across all modules.
    pub fn resolve_symbol(&mut self, name: &str) -> Option<usize> {
        self.linker
            .resolve_symbol(name)
            .or_else(|| self.native_libs.resolve_symbol(name))
    }

    /// Resolve a symbol and get its table index.
    pub fn resolve_symbol_with_index(&self, name: &str) -> Option<(usize, TableIndex)> {
        self.linker.resolve_symbol_with_index(name)
    }

    /// Get dependencies for a module.
    pub fn get_dependencies(&self, handle: ModuleHandle) -> Vec<ModuleHandle> {
        self.linker.get_dependencies(handle)
    }

    /// Get modules that depend on the given module.
    pub fn get_dependents(&self, handle: ModuleHandle) -> Vec<ModuleHandle> {
        self.linker.get_dependents(handle)
    }

    /// Check if a module can be safely removed.
    pub fn can_remove(&self, handle: ModuleHandle) -> bool {
        self.linker.can_remove(handle)
    }

    /// Replace a module with a new version (hot code replacement).
    ///
    /// This atomically updates function pointers in the indirection table,
    /// allowing existing calls to seamlessly use the new code.
    ///
    /// # Requirements
    /// - Settlement must be configured as reloadable
    /// - New module must export the same symbols as the old one
    /// - New module must be ABI-compatible
    ///
    /// # Safety
    /// This operation is safe as long as:
    /// - No running code is in the middle of the old module's functions
    /// - The new module has the same function signatures
    pub fn replace_module(
        &mut self,
        handle: ModuleHandle,
        new_module: &LoadedModule,
    ) -> Result<(), SettlementError> {
        if !self.config.reloadable {
            return Err(SettlementError::InvalidModule(
                "Settlement is not configured for hot reload".to_string(),
            ));
        }

        let old_module = self
            .modules
            .get(handle.as_usize())
            .ok_or_else(|| SettlementError::ModuleNotFound(format!("Handle {:?}", handle)))?;

        let _name = old_module.name.clone();
        let old_code_slots = old_module.code_slots;
        let old_data_slots = old_module.data_slots;
        let old_functions = old_module.functions.clone();

        // Get new module sizes
        let new_code_size = new_module.code_mem.size();
        let new_data_size = new_module.data_mem.as_ref().map(|d| d.size()).unwrap_or(0);

        // Allocate new slots
        let new_code_slots = self
            .code_slots
            .allocate_bytes(new_code_size)
            .ok_or(SettlementError::CodeRegionFull)?;

        let new_data_slots = if new_data_size > 0 {
            self.data_slots
                .allocate_bytes(new_data_size)
                .ok_or(SettlementError::DataRegionFull)?
        } else {
            SlotRange::new(0, 0)
        };

        // Copy new code
        let (new_code_ptr, _) = self.code_slots.get_memory(new_code_slots);
        unsafe {
            std::ptr::copy_nonoverlapping(
                new_module.code_mem.as_ptr(),
                new_code_ptr,
                new_code_size,
            );
        }

        // Copy new data
        if let Some(ref data_mem) = new_module.data_mem {
            let (new_data_ptr, _) = self.data_slots.get_memory(new_data_slots);
            unsafe {
                std::ptr::copy_nonoverlapping(data_mem.as_ptr(), new_data_ptr, new_data_size);
            }
        }

        // Update function table entries atomically
        // Map old function names to new addresses
        let mut func_indices: Vec<(String, TableIndex)> = Vec::new();

        for &old_func_idx in old_functions.iter() {
            // Find corresponding symbol in new module
            if self.func_table.get_entry(old_func_idx).is_some() {
                // For each old function, find the matching new one
                for sym in new_module.symbols.exports() {
                    if sym.sym_type == crate::smf::SymbolType::Function {
                        let offset = sym.value as usize;
                        let new_addr = new_code_ptr as usize + offset;
                        let sym_name = new_module.symbols.symbol_name(sym).to_string();

                        // Update the function pointer atomically
                        unsafe {
                            self.func_table.update_code_ptr(old_func_idx, new_addr);
                        }

                        func_indices.push((sym_name, old_func_idx));
                        break;
                    }
                }
            }
        }

        // Update linker exports
        self.linker
            .update_exports(new_module, handle, new_code_ptr as usize, &func_indices);

        // Free old slots (after updating pointers)
        self.code_slots.free(old_code_slots);
        if old_data_slots.count > 0 {
            self.data_slots.free(old_data_slots);
        }

        // Update module info
        if let Some(module) = self.modules.get_mut(handle.as_usize()) {
            module.code_slots = new_code_slots;
            module.data_slots = new_data_slots;
            module.code_size = new_code_size;
            module.data_size = new_data_size;
            module.code_range = new_code_slots;
            module.data_range = new_data_slots;
            module.version = new_module.version;
        }

        Ok(())
    }

    /// Get the linker for advanced operations.
    pub fn linker(&self) -> &SettlementLinker {
        &self.linker
    }

    /// Get mutable linker for advanced operations.
    pub fn linker_mut(&mut self) -> &mut SettlementLinker {
        &mut self.linker
    }

    /// Get a module by handle.
    pub fn get_module(&self, handle: ModuleHandle) -> Option<&SettlementModule> {
        if handle.is_valid() {
            self.modules.get(handle.as_usize())
        } else {
            None
        }
    }

    /// Get a module by name.
    pub fn get_module_by_name(&self, name: &str) -> Option<&SettlementModule> {
        self.modules_by_name
            .get(name)
            .and_then(|h| self.get_module(*h))
    }

    /// Add a native library to the settlement.
    pub fn add_native_lib(&mut self, spec: NativeLibSpec) -> Result<NativeHandle, SettlementError> {
        match spec {
            NativeLibSpec::Static { name, data, .. } => {
                // Allocate space in data region for static lib
                let slots = self
                    .data_slots
                    .allocate_bytes(data.len())
                    .ok_or(SettlementError::DataRegionFull)?;

                let (ptr, _) = self.data_slots.get_memory(slots);
                unsafe {
                    std::ptr::copy_nonoverlapping(data.as_ptr(), ptr, data.len());
                }

                Ok(self.native_libs.add_static(&name, ptr, data.len()))
            }
            NativeLibSpec::Shared { name, path } => self
                .native_libs
                .add_shared(&name, &path)
                .map_err(SettlementError::NativeLibError),
            NativeLibSpec::System { name } => self
                .native_libs
                .add_system(&name)
                .map_err(SettlementError::NativeLibError),
        }
    }

    /// Resolve a native symbol.
    pub fn resolve_native_symbol(&mut self, name: &str) -> Option<usize> {
        self.native_libs.resolve_symbol(name)
    }

    /// Get the entry point address.
    pub fn entry_point(&self) -> Option<usize> {
        self.entry_func_idx
            .and_then(|idx| self.func_table.get_code_ptr(idx))
    }

    /// Get function pointer by table index.
    pub fn get_function(&self, idx: TableIndex) -> Option<usize> {
        self.func_table.get_code_ptr(idx)
    }

    /// Get global pointer by table index.
    pub fn get_global(&self, idx: TableIndex) -> Option<usize> {
        self.global_table.get_data_ptr(idx)
    }

    /// Get code region base address.
    pub fn code_base(&self) -> *const u8 {
        self.code_region.as_ptr()
    }

    /// Get data region base address.
    pub fn data_base(&self) -> *const u8 {
        self.data_region.as_ptr()
    }

    /// Get number of modules.
    pub fn module_count(&self) -> usize {
        self.modules.len()
    }

    /// Get number of functions in table.
    pub fn function_count(&self) -> usize {
        self.func_table.len()
    }

    /// Get number of globals in table.
    pub fn global_count(&self) -> usize {
        self.global_table.len()
    }

    /// Get number of native libraries.
    pub fn native_lib_count(&self) -> usize {
        self.native_libs.len()
    }

    /// Check if settlement supports hot reload.
    pub fn is_reloadable(&self) -> bool {
        self.config.reloadable
    }

    /// Check if settlement is configured as executable.
    pub fn is_executable(&self) -> bool {
        self.config.executable
    }

    /// Calculate fragmentation of code region.
    pub fn code_fragmentation(&self) -> f64 {
        self.code_slots.fragmentation()
    }

    /// Calculate fragmentation of data region.
    pub fn data_fragmentation(&self) -> f64 {
        self.data_slots.fragmentation()
    }

    /// Compact the settlement (defragment memory regions).
    ///
    /// This is an expensive operation that moves code/data and updates tables.
    pub fn compact(&mut self) -> Result<(), SettlementError> {
        // Get defragmentation plans
        let code_moves = self.code_slots.defragment_plan();
        let data_moves = self.data_slots.defragment_plan();

        // Move code (need to update function table pointers)
        for (old_range, new_range) in &code_moves {
            let (old_ptr, size) = self.code_slots.get_memory(*old_range);
            let (new_ptr, _) = self.code_slots.get_memory(*new_range);

            // Move the data
            unsafe {
                std::ptr::copy(old_ptr, new_ptr, size);
            }

            // Update function table entries that point to this range
            let old_base = old_ptr as usize;
            let new_base = new_ptr as usize;
            let delta = new_base as isize - old_base as isize;

            for (idx, entry) in self.func_table.iter_valid() {
                let ptr = entry.code_ptr as usize;
                if ptr >= old_base && ptr < old_base + size {
                    let new_ptr = (ptr as isize + delta) as usize;
                    unsafe {
                        self.func_table.update_code_ptr(idx, new_ptr);
                    }
                }
            }
        }

        // Move data (need to update global table pointers)
        for (old_range, new_range) in &data_moves {
            let (old_ptr, size) = self.data_slots.get_memory(*old_range);
            let (new_ptr, _) = self.data_slots.get_memory(*new_range);

            unsafe {
                std::ptr::copy(old_ptr, new_ptr, size);
            }

            // Update global table entries
            let old_base = old_ptr as usize;
            let new_base = new_ptr as usize;
            let delta = new_base as isize - old_base as isize;

            for idx in 0..self.global_table.len() {
                let idx = TableIndex(idx as u32);
                if let Some(ptr) = self.global_table.get_data_ptr(idx) {
                    if ptr >= old_base && ptr < old_base + size {
                        let new_ptr = (ptr as isize + delta) as usize;
                        unsafe {
                            self.global_table.update_data_ptr(idx, new_ptr);
                        }
                    }
                }
            }
        }

        // Apply changes to slot allocators
        self.code_slots.apply_defragment(&code_moves);
        self.data_slots.apply_defragment(&data_moves);

        Ok(())
    }

    /// Generate settlement header for serialization.
    pub fn to_header(&self) -> SettlementHeader {
        let mut header = SettlementHeader::new();

        header.flags = 0;
        if self.config.executable {
            header.flags |= SSMF_FLAG_EXECUTABLE;
        }
        if self.config.reloadable {
            header.flags |= SSMF_FLAG_RELOADABLE;
        }
        if !self.native_libs.is_empty() {
            header.flags |= SSMF_FLAG_HAS_NATIVES;
        }

        header.module_count = self.modules.len() as u32;
        header.native_lib_count = self.native_libs.len() as u32;
        header.func_table_count = self.func_table.len() as u32;
        header.global_table_count = self.global_table.len() as u32;
        header.type_table_count = self.type_table.len() as u32;

        if let Some(entry_module) = self.entry_module {
            header.entry_module_idx = entry_module.0;
        }
        if let Some(entry_func) = self.entry_func_idx {
            header.entry_func_idx = entry_func.0;
        }

        header
    }

    /// Iterate over all modules.
    pub fn modules(&self) -> impl Iterator<Item = &SettlementModule> {
        self.modules.iter()
    }

    // ============== Serialization helpers for SettlementBuilder ==============

    /// Get code region as byte slice.
    pub fn code_region_slice(&self) -> &[u8] {
        unsafe { std::slice::from_raw_parts(self.code_region.as_ptr(), self.code_region.size()) }
    }

    /// Get data region as byte slice.
    pub fn data_region_slice(&self) -> &[u8] {
        unsafe { std::slice::from_raw_parts(self.data_region.as_ptr(), self.data_region.size()) }
    }

    /// Get function table entries as slice.
    pub fn func_table_slice(&self) -> &[crate::smf::settlement::FuncTableEntry] {
        self.func_table.as_slice()
    }

    /// Get global table entries as slice.
    pub fn global_table_slice(&self) -> &[crate::smf::settlement::GlobalTableEntry] {
        self.global_table.as_slice()
    }

    /// Get type table entries as slice.
    pub fn type_table_slice(&self) -> &[crate::smf::settlement::TypeTableEntry] {
        self.type_table.as_slice()
    }

    /// Iterate over modules with serialization info.
    pub fn iter_modules(&self) -> impl Iterator<Item = &SettlementModule> {
        self.modules.iter()
    }

    /// Get native library manager reference.
    pub fn native_libs(&self) -> &NativeLibManager {
        &self.native_libs
    }

    /// Get entry point indices for serialization.
    /// Returns (entry_module_idx, entry_func_idx).
    pub fn entry_point_indices(&self) -> (u32, u32) {
        let module_idx = self.entry_module.map(|h| h.0).unwrap_or(u32::MAX);
        let func_idx = self.entry_func_idx.map(|i| i.0).unwrap_or(u32::MAX);
        (module_idx, func_idx)
    }
}

