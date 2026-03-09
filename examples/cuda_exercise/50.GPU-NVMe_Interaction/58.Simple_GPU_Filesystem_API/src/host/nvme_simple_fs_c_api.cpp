/**
 * @file nvme_simple_fs_c_api.cpp
 * @brief C API wrapper implementation
 *
 * @author Module 58 Developer
 * @date 2025-10-25
 */

#include "nvme_simple_fs_c_api.h"
#include "nvme_simple_fs.h"
#include <cstring>
#include <string>

// Thread-local error message storage
thread_local std::string g_last_error;

static void set_error(const std::string& msg) {
    g_last_error = msg;
}

// ---- Filesystem lifecycle ----

nvme_fs_handle_t* nvme_fs_create(void* nvme_device,
                                 uint64_t start_lba,
                                 uint64_t total_blocks,
                                 uint64_t block_size) {
    try {
        auto fs = nvme_fs::create_filesystem(nvme_device, start_lba,
                                             total_blocks, block_size);
        return reinterpret_cast<nvme_fs_handle_t*>(fs.release());
    } catch (const std::exception& e) {
        set_error(e.what());
        return nullptr;
    }
}

nvme_fs_handle_t* nvme_fs_open(void* nvme_device, uint64_t start_lba) {
    try {
        auto fs = nvme_fs::open_filesystem(nvme_device, start_lba);
        return reinterpret_cast<nvme_fs_handle_t*>(fs.release());
    } catch (const std::exception& e) {
        set_error(e.what());
        return nullptr;
    }
}

void nvme_fs_close(nvme_fs_handle_t* fs) {
    if (fs) {
        auto* filesystem = reinterpret_cast<nvme_fs::NvmeSimpleFilesystem*>(fs);
        delete filesystem;
    }
}

int nvme_fs_format(nvme_fs_handle_t* fs) {
    if (!fs) return -1;

    try {
        auto* filesystem = reinterpret_cast<nvme_fs::NvmeSimpleFilesystem*>(fs);
        filesystem->format();
        return 0;
    } catch (const std::exception& e) {
        set_error(e.what());
        return -1;
    }
}

// ---- File operations ----

uint32_t nvme_fs_save_file(nvme_fs_handle_t* fs,
                           const char* filename,
                           const void* data,
                           size_t size_bytes) {
    if (!fs || !filename || !data) return 0;

    try {
        auto* filesystem = reinterpret_cast<nvme_fs::NvmeSimpleFilesystem*>(fs);
        return filesystem->save_file(filename, data, size_bytes);
    } catch (const std::exception& e) {
        set_error(e.what());
        return 0;
    }
}

size_t nvme_fs_read_file(nvme_fs_handle_t* fs,
                         const char* filename,
                         void* buffer,
                         size_t buffer_size) {
    if (!fs || !filename || !buffer) return 0;

    try {
        auto* filesystem = reinterpret_cast<nvme_fs::NvmeSimpleFilesystem*>(fs);
        return filesystem->read_file(filename, buffer, buffer_size);
    } catch (const std::exception& e) {
        set_error(e.what());
        return 0;
    }
}

int nvme_fs_write_file(nvme_fs_handle_t* fs,
                       const char* filename,
                       uint64_t offset,
                       const void* data,
                       size_t size_bytes) {
    if (!fs || !filename || !data) return -1;

    try {
        auto* filesystem = reinterpret_cast<nvme_fs::NvmeSimpleFilesystem*>(fs);
        filesystem->write_file(filename, offset, data, size_bytes);
        return 0;
    } catch (const std::exception& e) {
        set_error(e.what());
        return -1;
    }
}

int nvme_fs_delete_file(nvme_fs_handle_t* fs, const char* filename) {
    if (!fs || !filename) return -1;

    try {
        auto* filesystem = reinterpret_cast<nvme_fs::NvmeSimpleFilesystem*>(fs);
        return filesystem->delete_file(filename) ? 1 : 0;
    } catch (const std::exception& e) {
        set_error(e.what());
        return -1;
    }
}

int nvme_fs_get_file_info(nvme_fs_handle_t* fs,
                          const char* filename,
                          nvme_fs_file_info_t* info) {
    if (!fs || !filename || !info) return -1;

    try {
        auto* filesystem = reinterpret_cast<nvme_fs::NvmeSimpleFilesystem*>(fs);
        nvme_fs::FileEntry entry = filesystem->get_file_info(filename);

        std::strncpy(info->name, entry.name.c_str(), sizeof(info->name) - 1);
        info->name[sizeof(info->name) - 1] = '\0';
        info->file_id = entry.file_id;
        info->size_bytes = entry.size_bytes;
        info->created_time = entry.created_time;
        info->modified_time = entry.modified_time;
        info->checksum = entry.checksum;

        return 0;
    } catch (const std::exception& e) {
        set_error(e.what());
        return -1;
    }
}

int nvme_fs_get_file_node(nvme_fs_handle_t* fs,
                          const char* filename,
                          nvme_fs_node_t* node) {
    if (!fs || !filename || !node) return -1;

    try {
        auto* filesystem = reinterpret_cast<nvme_fs::NvmeSimpleFilesystem*>(fs);
        nvme_fs::LbaNode lba_node = filesystem->get_file_node(filename);

        node->start_lba = lba_node.start_lba;
        node->length = lba_node.length;
        node->file_id = lba_node.file_id;
        node->flags = lba_node.flags;

        return 0;
    } catch (const std::exception& e) {
        set_error(e.what());
        return -1;
    }
}

size_t nvme_fs_list_files(nvme_fs_handle_t* fs,
                          nvme_fs_file_info_t* files,
                          size_t max_files) {
    if (!fs || !files) return 0;

    try {
        auto* filesystem = reinterpret_cast<nvme_fs::NvmeSimpleFilesystem*>(fs);
        std::vector<nvme_fs::FileEntry> file_list = filesystem->list_files();

        size_t count = std::min(file_list.size(), max_files);
        for (size_t i = 0; i < count; ++i) {
            std::strncpy(files[i].name, file_list[i].name.c_str(),
                        sizeof(files[i].name) - 1);
            files[i].name[sizeof(files[i].name) - 1] = '\0';
            files[i].file_id = file_list[i].file_id;
            files[i].size_bytes = file_list[i].size_bytes;
            files[i].created_time = file_list[i].created_time;
            files[i].modified_time = file_list[i].modified_time;
            files[i].checksum = file_list[i].checksum;
        }

        return count;
    } catch (const std::exception& e) {
        set_error(e.what());
        return 0;
    }
}

// ---- Node-based I/O ----

int nvme_fs_read_node(nvme_fs_handle_t* fs,
                      const nvme_fs_node_t* node,
                      uint64_t offset_bytes,
                      void* buffer,
                      size_t size_bytes) {
    if (!fs || !node || !buffer) return -1;

    try {
        auto* filesystem = reinterpret_cast<nvme_fs::NvmeSimpleFilesystem*>(fs);

        nvme_fs::LbaNode lba_node;
        lba_node.start_lba = node->start_lba;
        lba_node.length = node->length;
        lba_node.file_id = node->file_id;
        lba_node.flags = node->flags;

        filesystem->read_node(lba_node, offset_bytes, buffer, size_bytes);
        return 0;
    } catch (const std::exception& e) {
        set_error(e.what());
        return -1;
    }
}

int nvme_fs_write_node(nvme_fs_handle_t* fs,
                       const nvme_fs_node_t* node,
                       uint64_t offset_bytes,
                       const void* data,
                       size_t size_bytes) {
    if (!fs || !node || !data) return -1;

    try {
        auto* filesystem = reinterpret_cast<nvme_fs::NvmeSimpleFilesystem*>(fs);

        nvme_fs::LbaNode lba_node;
        lba_node.start_lba = node->start_lba;
        lba_node.length = node->length;
        lba_node.file_id = node->file_id;
        lba_node.flags = node->flags;

        filesystem->write_node(lba_node, offset_bytes, data, size_bytes);
        return 0;
    } catch (const std::exception& e) {
        set_error(e.what());
        return -1;
    }
}

// ---- Space management ----

size_t nvme_fs_garbage_collect(nvme_fs_handle_t* fs) {
    if (!fs) return 0;

    try {
        auto* filesystem = reinterpret_cast<nvme_fs::NvmeSimpleFilesystem*>(fs);
        return filesystem->garbage_collect();
    } catch (const std::exception& e) {
        set_error(e.what());
        return 0;
    }
}

int nvme_fs_get_stats(nvme_fs_handle_t* fs, nvme_fs_stats_t* stats) {
    if (!fs || !stats) return -1;

    try {
        auto* filesystem = reinterpret_cast<nvme_fs::NvmeSimpleFilesystem*>(fs);
        uint64_t total, used, free;
        filesystem->get_stats(total, used, free);

        stats->total_bytes = total;
        stats->used_bytes = used;
        stats->free_bytes = free;
        stats->num_files = filesystem->list_files().size();

        return 0;
    } catch (const std::exception& e) {
        set_error(e.what());
        return -1;
    }
}

int nvme_fs_flush(nvme_fs_handle_t* fs) {
    if (!fs) return -1;

    try {
        auto* filesystem = reinterpret_cast<nvme_fs::NvmeSimpleFilesystem*>(fs);
        filesystem->flush_metadata();
        return 0;
    } catch (const std::exception& e) {
        set_error(e.what());
        return -1;
    }
}

// ---- Error handling ----

const char* nvme_fs_get_last_error(void) {
    return g_last_error.c_str();
}
