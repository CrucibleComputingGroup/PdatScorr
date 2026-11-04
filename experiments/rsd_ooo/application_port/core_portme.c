#include "coremark.h"
/* Standard 2K validation input; actual mcycle is the time unit. */
volatile ee_s32 seed1_volatile = 0x3415;
volatile ee_s32 seed2_volatile = 0x3415;
volatile ee_s32 seed3_volatile = 0x66;
volatile ee_s32 seed4_volatile = ITERATIONS;
volatile ee_s32 seed5_volatile = 0;
ee_u32 default_num_contexts = 1;
static CORE_TICKS start_tick, stop_tick;
static CORE_TICKS tick(void) {
  CORE_TICKS t;
  __asm__ volatile("csrr %0, mcycle" : "=r"(t) :: "memory");
  return t;
}
void start_time(void) { start_tick = tick(); }
void stop_time(void) { stop_tick = tick(); }
CORE_TICKS get_time(void) { return stop_tick - start_tick; }
/* Nominal conversion is only for upstream display; no score is reported. */
secs_ret time_in_secs(CORE_TICKS t) { return t / 1000000; }
void portable_init(core_portable *p, int *argc, char *argv[]) {
  p->portable_id = 1;
}
void portable_fini(core_portable *p) { p->portable_id = 0; }
