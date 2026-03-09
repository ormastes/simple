project(69_MoE_NVMe_Complete_System CUDA CXX)
set(MODULE ${PROJECT_NAME})
add_subdirectory(src)
add_subdirectory(test)

# Example executables
add_executable(${MODULE}_text_gen examples/text_generation.cpp)
target_link_libraries(${MODULE}_text_gen PRIVATE ${MODULE}_lib)
add_profiling_targets(${MODULE}_text_gen)

add_executable(${MODULE}_qa examples/question_answering.cpp)
target_link_libraries(${MODULE}_qa PRIVATE ${MODULE}_lib)
add_profiling_targets(${MODULE}_qa)
