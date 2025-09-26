#pragma once

#include <inttypes.h>
#include <stdio.h>

#include "clock.h"

#define log(fmt, ...)                \
  do {                               \
    printf(fmt "\n", ##__VA_ARGS__); \
    fflush(stdout);                  \
  } while (0);

#define log_clk(fmt, ...)                                         \
  do {                                                            \
    printf("[%" PRIu64 "] " fmt "\n", get_time(), ##__VA_ARGS__); \
    fflush(stdout);                                               \
  } while (0);

#define log_dbg(fmt, ...)                     \
  do {                                        \
    fprintf(stderr, fmt "\n", ##__VA_ARGS__); \
    fflush(stderr);                           \
  } while (0);

#define panic(fmt, ...)                        \
  do {                                         \
    printf("PANIC: " fmt "\n", ##__VA_ARGS__); \
    exit(EXIT_FAILURE);                        \
  } while (0)
