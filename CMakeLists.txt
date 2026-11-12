# kategoria: categories computed with — finite and presented categories, functors, limits, set-valued functors and monoidal
# theories, with every claim answered by evidence.
#
# Every module is a header-only target kategoria::<module>. kategoria uses the targets of calx (its checks) and morphe: inside
# the infrastructure, the siblings under foundations/ (each added here when no larger project has added it). Built on its own,
# kategoria builds its checks (KATEGORIA_CHECKS); added to a larger project, only when asked.

cmake_minimum_required(VERSION 3.20)
project(kategoria VERSION 0.1.0 LANGUAGES CXX)

if(CMAKE_SOURCE_DIR STREQUAL CMAKE_CURRENT_SOURCE_DIR)
  set(KATEGORIA_TOP_LEVEL ON)
else()
  set(KATEGORIA_TOP_LEVEL OFF)
endif()
option(KATEGORIA_CHECKS "Build kategoria's checks" ${KATEGORIA_TOP_LEVEL})

if(NOT DEFINED CMAKE_CXX_STANDARD)
  set(CMAKE_CXX_STANDARD 20)
  set(CMAKE_CXX_STANDARD_REQUIRED ON)
  set(CMAKE_CXX_EXTENSIONS OFF)
endif()
if(NOT CMAKE_BUILD_TYPE AND NOT CMAKE_CONFIGURATION_TYPES)
  set(CMAKE_BUILD_TYPE Release)
endif()

# kategoria_sibling(<directory> <a target it defines>): the sibling library, added once.
function(kategoria_sibling directory target)
  if(NOT TARGET ${target})
    if(EXISTS ${CMAKE_CURRENT_SOURCE_DIR}/../${directory}/CMakeLists.txt)
      add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/../${directory} ${CMAKE_BINARY_DIR}/${directory})
    else()
      message(FATAL_ERROR "kategoria needs ${directory}: build it inside the infrastructure (foundations/${directory}).")
    endif()
  endif()
endfunction()

kategoria_sibling(calx calx::linalg)
kategoria_sibling(morphe morphe::topology)
if(KATEGORIA_CHECKS)
  enable_testing()
endif()

# kategoria_module(<name> [LIBRARIES ...] [CHECK_LIBRARIES ...]): the target kategoria::<name> and, with the checks,
# check_kategoria_<name>, which may use more libraries than the module does.
function(kategoria_module name)
  cmake_parse_arguments(ARG "" "" "LIBRARIES;CHECK_LIBRARIES" ${ARGN})
  add_library(kategoria_${name} INTERFACE)
  add_library(kategoria::${name} ALIAS kategoria_${name})
  target_include_directories(kategoria_${name} INTERFACE ${CMAKE_CURRENT_SOURCE_DIR}/${name}/include)
  target_compile_features(kategoria_${name} INTERFACE cxx_std_20)
  target_link_libraries(kategoria_${name} INTERFACE ${ARG_LIBRARIES})
  if(KATEGORIA_CHECKS AND EXISTS ${CMAKE_CURRENT_SOURCE_DIR}/${name}/tests/check_${name}.cpp)
    calx_add_check(check_kategoria_${name} SOURCES ${name}/tests/check_${name}.cpp LIBRARIES kategoria::${name} ${ARG_CHECK_LIBRARIES})
  endif()
endfunction()

# The modules in their order (decision 0002).
kategoria_module(kernel)
kategoria_module(finite LIBRARIES kategoria::kernel CHECK_LIBRARIES morphe::algebra)
kategoria_module(functors LIBRARIES kategoria::finite CHECK_LIBRARIES morphe::algebra)
kategoria_module(limits LIBRARIES kategoria::functors CHECK_LIBRARIES morphe::algebra)
kategoria_module(sets LIBRARIES kategoria::functors CHECK_LIBRARIES kategoria::limits morphe::algebra)
kategoria_module(presentations LIBRARIES kategoria::finite CHECK_LIBRARIES kategoria::functors morphe::algebra)
kategoria_module(monoidal LIBRARIES kategoria::finite morphe::combinatorics)
kategoria_module(script LIBRARIES kategoria::limits kategoria::sets kategoria::presentations kategoria::monoidal morphe::formal morphe::algebra)
