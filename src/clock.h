#pragma once

#include <stdint.h>

typedef uint64_t time_ns_t;

void reset_time();
time_ns_t get_time();
void increment_time(time_ns_t dt);