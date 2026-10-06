#include <util.h>

// Should not be inlined, because we expect arguments
// in particular registers.
//__attribute__((noinline))

extern int rv32_atest(int);

int mymain () {
  int fail_flag, result;
  int cnt;

  char *hello_msg = "Starting RV32 Test1!\n";
  char *pass_msg = "\nTest passed :-)\n";
  char *fail_msg = "\nTest failed :-(((((\n";

  prints(hello_msg);

  fail_flag = rv32_atest(0);

  if (fail_flag == 0) {
    prints(pass_msg);
  } else {
    prints(fail_msg);
  }

  return 0;
   
}

