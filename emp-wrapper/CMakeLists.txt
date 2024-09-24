cmake_minimum_required(VERSION 3.9)
project(emp-zkc)

find_package(emp-zk REQUIRED)
find_package(emp-tool REQUIRED)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_VERBOSE_MAKEFILE ON)

set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -pthread -Wall -funroll-loops -Wno-ignored-attributes -Wno-unused-result")
message("${Blue}-- Platform: ${CMAKE_SYSTEM_PROCESSOR}${ColourReset}")
IF(${CMAKE_SYSTEM_PROCESSOR} MATCHES "(aarch64)|(arm64)")
    set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -march=armv8-a+simd+crypto+crc")
ELSE(${CMAKE_SYSTEM_PROCESSOR} MATCHES "(aarch64)|(arm64)")
    set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -march=native -maes -mrdseed")
ENDIF(${CMAKE_SYSTEM_PROCESSOR} MATCHES "(aarch64)|(arm64)" )
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${CMAKE_C_FLAGS} -std=c++11")

include_directories(${EMP-TOOL_INCLUDE_DIRS} ${EMP-ZK_INCLUDE_DIRS})
link_libraries(${EMP-TOOL_LIBRARIES} ${EMP-ZK_LIBRARIES})
add_library(emp-zkc SHARED emp-zkc.cpp emp-zkc.hpp)
target_compile_features(emp-zkc PRIVATE cxx_std_20)
