cmake_minimum_required(VERSION 3.20)
project(alive2-ebpf-poc LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE Release)
endif()

set(ALIVE2_SRC "${CMAKE_CURRENT_SOURCE_DIR}/third_party/alive2")
set(ALIVE2_BUILD "${ALIVE2_SRC}/build" CACHE PATH "Alive2 build directory")
set(Z3_INCLUDE_DIR "/opt/homebrew/opt/z3/include" CACHE PATH "Z3 headers")
set(Z3_LIBRARY "/opt/homebrew/opt/z3/lib/libz3.dylib" CACHE FILEPATH "Z3 library")

function(alive2_link target)
  target_include_directories(${target} PRIVATE
    "${ALIVE2_SRC}"
    "${ALIVE2_BUILD}"
    "${Z3_INCLUDE_DIR}")
  target_link_libraries(${target} PRIVATE
    "${ALIVE2_BUILD}/libir.a"
    "${ALIVE2_BUILD}/libsmt.a"
    "${ALIVE2_BUILD}/libtools.a"
    "${ALIVE2_BUILD}/libutil.a"
    "${Z3_LIBRARY}")
  if(APPLE)
    get_filename_component(Z3_LIB_DIR "${Z3_LIBRARY}" DIRECTORY)
    target_link_options(${target} PRIVATE "-Wl,-rpath,${Z3_LIB_DIR}")
  endif()
endfunction()

add_executable(direct_ir src/direct_ir.cpp)
alive2_link(direct_ir)
target_compile_options(direct_ir PRIVATE -Wall -Wextra -Wno-unused-parameter)

set(EBPF_FRONTEND
  src/ebpf_decode.cpp
  src/ebpf_ref.cpp
  src/ebpf_lift.cpp
  src/ebpf_run.cpp
  src/ebpf_check.cpp)

add_executable(ebpf_test ${EBPF_FRONTEND} src/ebpf_test.cpp)
alive2_link(ebpf_test)
target_compile_options(ebpf_test PRIVATE -Wall -Wextra -Wno-unused-parameter)

add_executable(ebpf_file ${EBPF_FRONTEND} src/ebpf_file.cpp)
alive2_link(ebpf_file)
target_compile_options(ebpf_file PRIVATE -Wall -Wextra -Wno-unused-parameter)
