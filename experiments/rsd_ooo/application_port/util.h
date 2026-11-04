/* riscv-tests environment API: real cycle reads and no host syscall. */
#ifndef PSCORR_APP_UTIL_H
#define PSCORR_APP_UTIL_H
#define read_csr(reg) ({ unsigned long value; \
  __asm__ volatile ("csrr %0, " #reg : "=r"(value) :: "memory"); value; })
static inline void setStats(int enabled) { (void)enabled; }
#endif
