cmake_minimum_required(VERSION 3.6)
project(BartlettsMostlyCopying)

set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS}")

set(SOURCE_FILES main.c)
add_executable(BartlettsMostlyCopying ${SOURCE_FILES})