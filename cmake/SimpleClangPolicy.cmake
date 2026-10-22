# Attach a controller-written effective-policy stamp to every C-family object
# in one target. The Simple policy gate must run before `cmake --build` and
# atomically replace the stamp whenever its required dependency digest changes.
# This module never decides policy or claims that a compiler launcher ran.

function(simple_clang_policy_attach target stamp)
  # This first adapter is qualified only against Ninja's object dependency
  # graph. Visual Studio and Xcode do not implement OBJECT_DEPENDS.
  if(NOT CMAKE_GENERATOR STREQUAL "Ninja")
    message(FATAL_ERROR "simple_clang_policy_attach: Ninja generator required")
  endif()
  if(NOT TARGET "${target}")
    message(FATAL_ERROR "simple_clang_policy_attach: unknown target ${target}")
  endif()
  if(NOT IS_ABSOLUTE "${stamp}" OR NOT EXISTS "${stamp}" OR
     IS_DIRECTORY "${stamp}" OR IS_SYMLINK "${stamp}")
    message(FATAL_ERROR "simple_clang_policy_attach: stamp must be an existing regular absolute file")
  endif()

  get_target_property(_prior_stamp "${target}" SIMPLE_CLANG_POLICY_STAMP)
  if(_prior_stamp)
    message(FATAL_ERROR "simple_clang_policy_attach: target already attached")
  endif()
  get_target_property(_sources "${target}" SOURCES)
  if(NOT _sources)
    message(FATAL_ERROR "simple_clang_policy_attach: target has no declared sources")
  endif()

  set(_attached 0)
  foreach(_source IN LISTS _sources)
    # Generator expressions need configuration-specific source resolution.
    # Refuse partial attachment rather than silently omitting an object.
    if(_source MATCHES "\\$<")
      message(FATAL_ERROR "simple_clang_policy_attach: generator-expression source needs explicit resolution")
    endif()
    get_source_file_property(_header "${_source}" HEADER_FILE_ONLY
      TARGET_DIRECTORY "${target}")
    if(_header)
      continue()
    endif()
    get_source_file_property(_language "${_source}" LANGUAGE
      TARGET_DIRECTORY "${target}")
    if(_language)
      if(NOT _language MATCHES "^(C|CXX|OBJC|OBJCXX)$")
        message(FATAL_ERROR "simple_clang_policy_attach: unsupported compiled language ${_language}")
      endif()
    elseif(_source MATCHES "\\.(c|cc|cpp|cxx|c\\+\\+|C|m|mm)$")
      # CMake infers one of the supported C-family languages.
    elseif(_source MATCHES "\\.(h|hh|hpp|hxx|inc|inl)$")
      continue()
    else()
      message(FATAL_ERROR "simple_clang_policy_attach: source language unknown for ${_source}")
    endif()
    set_property(SOURCE "${_source}" TARGET_DIRECTORY "${target}"
      APPEND PROPERTY OBJECT_DEPENDS "${stamp}")
    math(EXPR _attached "${_attached} + 1")
  endforeach()
  if(_attached EQUAL 0)
    message(FATAL_ERROR "simple_clang_policy_attach: no C-family objects found")
  endif()
  set_property(TARGET "${target}" PROPERTY SIMPLE_CLANG_POLICY_STAMP "${stamp}")
endfunction()
