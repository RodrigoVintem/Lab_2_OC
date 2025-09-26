#include "clock.h"

time_ns_t current_time = 0;

void reset_time() { current_time = 0; }
time_ns_t get_time() { return current_time; }
void increment_time(time_ns_t dt) { current_time += dt; }