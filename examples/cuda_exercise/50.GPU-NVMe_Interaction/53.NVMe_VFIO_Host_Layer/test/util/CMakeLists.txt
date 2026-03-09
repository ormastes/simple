# Utility programs for Module 53

add_executable(detect_dbc_support detect_dbc_support.cpp)
target_link_libraries(detect_dbc_support PRIVATE device_detector)
