# file_utils.cmake - Utilities for creating and managing test data files
# Provides functions for creating contiguous files for storage testing

# Function to create a consecutive (contiguous) file for testing
# Usage: create_consecutive_file(TARGET_NAME OUTPUT_DIR OUTPUT_FILE SIZE_MB)
# Creates a file at OUTPUT_PATH with SIZE_MB megabytes, attempting to make it physically contiguous
# The file is only created if it doesn't already exist
# If creation fails after 10 attempts, the build will fail with an error
function(create_consecutive_file TARGET_NAME OUTPUT_DIR OUTPUT_FILE SIZE_MB)
    # Calculate size in bytes
    math(EXPR SIZE_BYTES "${SIZE_MB} * 1024 * 1024")

    # Full output path
    set(OUTPUT_PATH "${OUTPUT_DIR}/${OUTPUT_FILE}" ABSOLUTE)

    # compile  options in parent scope
    add_compile_definitions(DATA_DIR="${CMAKE_BINARY_DIR}/${OUTPUT_DIR}" PARENT_SCOPE)

    # Get the directory path
    get_filename_component(OUTPUT_DIR "${OUTPUT_PATH}" DIRECTORY)

    # Get the absolute path relative to build directory
    if(NOT IS_ABSOLUTE "${OUTPUT_PATH}")
        set(OUTPUT_PATH "${CMAKE_CURRENT_BINARY_DIR}/${OUTPUT_PATH}")
        set(OUTPUT_DIR "${CMAKE_CURRENT_BINARY_DIR}/${OUTPUT_DIR}")
    endif()

    # Create script file for file generation
    set(SCRIPT_FILE "${CMAKE_CURRENT_BINARY_DIR}/create_${TARGET_NAME}.sh")
    file(WRITE "${SCRIPT_FILE}" "#!/bin/bash
set -e

OUTPUT_FILE='${OUTPUT_PATH}'
OUTPUT_DIR='${OUTPUT_DIR}'
SIZE_BYTES=${SIZE_BYTES}
SIZE_MB=${SIZE_MB}
MAX_ATTEMPTS=10

# Create directory if it doesn't exist
mkdir -p \"$OUTPUT_DIR\"

# Check if file already exists
if [ -f \"$OUTPUT_FILE\" ]; then
    EXISTING_SIZE=$(stat -c%s \"$OUTPUT_FILE\" 2>/dev/null || echo 0)
    if [ \"$EXISTING_SIZE\" -eq \"$SIZE_BYTES\" ]; then
        echo \"File already exists with correct size: $OUTPUT_FILE\"
        echo \"Skipping creation (to preserve any manual defragmentation)\"
        exit 0
    else
        echo \"File exists but has wrong size ($EXISTING_SIZE bytes vs $SIZE_BYTES bytes expected)\"
        echo \"Removing and recreating...\"
        rm -f \"$OUTPUT_FILE\"
    fi
fi

# Try to create the file with multiple attempts
echo \"Attempting to create consecutive file (up to $MAX_ATTEMPTS attempts)...\"

for attempt in $(seq 1 $MAX_ATTEMPTS); do
    echo \"Attempt $attempt of $MAX_ATTEMPTS...\"

    # Strategy 1: Use fallocate for pre-allocation (Linux)
    if command -v fallocate >/dev/null 2>&1; then
        echo \"  Using fallocate for contiguous allocation...\"
        if fallocate -l $SIZE_BYTES \"$OUTPUT_FILE\" 2>/dev/null; then
            echo \"  fallocate succeeded\"

            # Fill with pattern
            echo \"  Writing pattern...\"
            python3 -c \"
import sys
with open('$OUTPUT_FILE', 'r+b') as f:
    chunk_size = 1024 * 1024  # 1 MB chunks
    for offset in range(0, $SIZE_BYTES, chunk_size):
        size = min(chunk_size, $SIZE_BYTES - offset)
        data = bytes([(offset + i) % 256 for i in range(size)])
        f.write(data)
    f.flush()
\" 2>/dev/null || {
                # Fallback if python3 not available: use dd with pattern from /dev/zero
                dd if=/dev/zero of=\"$OUTPUT_FILE\" bs=1M count=$SIZE_MB conv=notrunc 2>/dev/null || true
            }

            # Sync to disk
            sync

            # Verify size
            ACTUAL_SIZE=$(stat -c%s \"$OUTPUT_FILE\" 2>/dev/null || echo 0)
            if [ \"$ACTUAL_SIZE\" -eq \"$SIZE_BYTES\" ]; then
                echo \"Successfully created file: $OUTPUT_FILE\"
                echo \"Size: $ACTUAL_SIZE bytes\"

                # Check fragmentation and provide defrag command if needed
                if command -v filefrag >/dev/null 2>&1; then
                    echo \"\"
                    echo \"Fragmentation check:\"
                    EXTENTS=$(filefrag \"$OUTPUT_FILE\" | grep -oP '[0-9]+(?= extent)' || echo \"unknown\")
                    filefrag -v \"$OUTPUT_FILE\" 2>/dev/null | head -n 10 || true
                    echo \"\"
                    if [ \"$EXTENTS\" = \"1\" ]; then
                        echo \"✓ File is perfectly contiguous (1 extent)\"
                    elif [ \"$EXTENTS\" != \"unknown\" ]; then
                        echo \"⚠ File has $EXTENTS extents (fragmented)\"
                        echo \"To make it contiguous, run:\"
                        echo \"  sudo e4defrag $OUTPUT_FILE\"
                        echo \"Then verify with:\"
                        echo \"  filefrag -v $OUTPUT_FILE\"
                    fi
                fi

                exit 0
            else
                echo \"  Size mismatch: got $ACTUAL_SIZE, expected $SIZE_BYTES\"
                rm -f \"$OUTPUT_FILE\"
            fi
        else
            echo \"  fallocate failed, trying fallback method...\"
        fi
    fi

    # Strategy 2: Fallback - write file in one go with dd
    echo \"  Using dd for file creation...\"
    if dd if=/dev/zero of=\"$OUTPUT_FILE\" bs=1M count=$SIZE_MB oflag=direct 2>/dev/null; then
        sync
        ACTUAL_SIZE=$(stat -c%s \"$OUTPUT_FILE\" 2>/dev/null || echo 0)
        if [ \"$ACTUAL_SIZE\" -eq \"$SIZE_BYTES\" ]; then
            echo \"Successfully created file with dd: $OUTPUT_FILE\"

            # Check fragmentation
            if command -v filefrag >/dev/null 2>&1; then
                echo \"\"
                EXTENTS=$(filefrag \"$OUTPUT_FILE\" | grep -oP '[0-9]+(?= extent)' || echo \"unknown\")
                if [ \"$EXTENTS\" = \"1\" ]; then
                    echo \"✓ File is perfectly contiguous (1 extent)\"
                elif [ \"$EXTENTS\" != \"unknown\" ]; then
                    echo \"⚠ File has $EXTENTS extents. To defragment: sudo e4defrag $OUTPUT_FILE\"
                fi
            fi

            exit 0
        fi
    fi

    # Clean up failed attempt
    rm -f \"$OUTPUT_FILE\"

    # Wait before retry (exponential backoff)
    if [ $attempt -lt $MAX_ATTEMPTS ]; then
        sleep_time=$(( attempt ))
        echo \"  Waiting $sleep_time seconds before retry...\"
        sleep $sleep_time
    fi
done

# If we get here, all attempts failed
echo \"ERROR: Failed to create consecutive file after $MAX_ATTEMPTS attempts\"
echo \"File: $OUTPUT_FILE\"
exit 1
")

    # Make the script executable
    file(CHMOD "${SCRIPT_FILE}" PERMISSIONS OWNER_READ OWNER_WRITE OWNER_EXECUTE GROUP_READ GROUP_EXECUTE WORLD_READ WORLD_EXECUTE)

    # Create the custom target
    add_custom_target(${TARGET_NAME}
        COMMAND ${CMAKE_COMMAND} -E echo "=== Creating consecutive test file ==="
        COMMAND ${CMAKE_COMMAND} -E echo "Target: ${OUTPUT_PATH}"
        COMMAND ${CMAKE_COMMAND} -E echo "Size: ${SIZE_MB} MB (${SIZE_BYTES} bytes)"
        COMMAND bash "${SCRIPT_FILE}"
        WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
        COMMENT "Creating consecutive test file: ${OUTPUT_PATH}"
        VERBATIM
    )

    # Make this target run automatically as part of ALL
    add_custom_target(${TARGET_NAME}_auto ALL DEPENDS ${TARGET_NAME})

    message(STATUS "Added target '${TARGET_NAME}' to create consecutive file: ${OUTPUT_PATH} (${SIZE_MB} MB)")
endfunction()

# Function to verify file contiguity (informational only, doesn't fail build)
function(verify_file_contiguity FILE_PATH)
    if(NOT IS_ABSOLUTE "${FILE_PATH}")
        set(FILE_PATH "${CMAKE_CURRENT_BINARY_DIR}/${FILE_PATH}")
    endif()

    add_custom_target(verify_contiguity_${FILE_PATH}
        COMMAND bash -c "
            if [ ! -f '${FILE_PATH}' ]; then
                echo 'File does not exist: ${FILE_PATH}'
                exit 0
            fi

            echo 'Checking file contiguity: ${FILE_PATH}'

            if command -v filefrag >/dev/null 2>&1; then
                echo ''
                echo 'Fragmentation report (filefrag):'
                filefrag -v '${FILE_PATH}'

                EXTENTS=\\$\\$(filefrag '${FILE_PATH}' | grep -oP '\\d+(?= extent)')
                echo ''
                if [ \"$$EXTENTS\" -eq \"1\" ]; then
                    echo '✓ File is perfectly contiguous (1 extent)'
                else
                    echo '⚠ File is fragmented into' $$EXTENTS 'extents'
                    echo 'Consider running: sudo e4defrag ${FILE_PATH}'
                fi
            else
                echo 'filefrag not available, cannot verify contiguity'
            fi

            if command -v hdparm >/dev/null 2>&1; then
                echo ''
                echo 'Physical block mapping (requires sudo):'
                sudo hdparm --fibmap '${FILE_PATH}' 2>/dev/null || echo 'hdparm requires root privileges'
            fi
        "
        WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
        COMMENT "Verifying contiguity of ${FILE_PATH}"
    )
endfunction()
