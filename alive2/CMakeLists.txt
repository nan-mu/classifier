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

set(ROCQ_STEP_BIN "${CMAKE_CURRENT_BINARY_DIR}/rocq/rocq-step")
set(UPSTREAM_SRC "${CMAKE_CURRENT_SOURCE_DIR}/rocq/upstream")
set(UPSTREAM_BUILD "${CMAKE_CURRENT_BINARY_DIR}/rocq/upstream")
file(GLOB_RECURSE UPSTREAM_SOURCES CONFIGURE_DEPENDS
  "${UPSTREAM_SRC}/*.v" "${UPSTREAM_SRC}/validator/*.ml"
  "${UPSTREAM_SRC}/Makefile")
add_custom_command(
  OUTPUT "${ROCQ_STEP_BIN}"
  COMMAND ${CMAKE_COMMAND} -E rm -rf "${UPSTREAM_BUILD}"
  COMMAND ${CMAKE_COMMAND} -E copy_directory "${UPSTREAM_SRC}" "${UPSTREAM_BUILD}"
  COMMAND opam exec --switch linux-ebpf -- make -C "${UPSTREAM_BUILD}"
  COMMAND ${CMAKE_COMMAND} -E make_directory "${CMAKE_CURRENT_BINARY_DIR}/rocq"
  COMMAND ${CMAKE_COMMAND} -E copy
          "${UPSTREAM_BUILD}/validator/debug_hooks.ml"
          "${UPSTREAM_BUILD}/validator/validation.ml"
          "${CMAKE_CURRENT_SOURCE_DIR}/rocq/rocq_step.ml"
          "${CMAKE_CURRENT_BINARY_DIR}/rocq/"
  COMMAND opam exec --switch linux-ebpf -- ocamlfind ocamlopt -w -a
          -package zarith -linkpkg -o "${ROCQ_STEP_BIN}"
          debug_hooks.ml validation.ml rocq_step.ml
  WORKING_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}/rocq"
  DEPENDS "${CMAKE_CURRENT_SOURCE_DIR}/rocq/rocq_step.ml" ${UPSTREAM_SOURCES}
  VERBATIM)
add_custom_target(rocq-step DEPENDS "${ROCQ_STEP_BIN}")

add_executable(ebpf-concrete
  src/ebpf_decode.cpp
  src/ebpf_lift.cpp
  src/ebpf_concrete.cpp)
alive2_link(ebpf-concrete)
target_compile_options(ebpf-concrete PRIVATE -Wall -Wextra -Wno-unused-parameter)
target_compile_definitions(ebpf-concrete PRIVATE
  "ROCQ_STEP=\"${ROCQ_STEP_BIN}\""
  "PIN_PATH=\"${CMAKE_CURRENT_SOURCE_DIR}/rocq/PIN\""
  "SOURCES_SHA_PATH=\"${CMAKE_CURRENT_SOURCE_DIR}/rocq/SOURCES.sha256\""
  "SEMANTICS_DIR=\"${UPSTREAM_SRC}\"")
add_dependencies(ebpf-concrete rocq-step)
add_custom_command(TARGET ebpf-concrete PRE_BUILD
  COMMAND /bin/sh -c
    "if grep -E 'symexec\\.h|ebpf_run\\.h|ebpf_ref' '${CMAKE_CURRENT_SOURCE_DIR}/src/ebpf_concrete.cpp'; then exit 1; fi; if grep -n sym_exec '${CMAKE_CURRENT_SOURCE_DIR}/src/ebpf_lift.cpp'; then exit 1; fi; if grep -n execute_ebpf '${CMAKE_CURRENT_SOURCE_DIR}/src/ebpf_lift.cpp'; then exit 1; fi"
  VERBATIM)
