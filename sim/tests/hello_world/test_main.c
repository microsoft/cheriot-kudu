#include <util.h>

// Should not be inlined, because we expect arguments
// in particular registers.
//__attribute__((noinline))

extern int hello_atest(int);

int mymain () {
  int fail_flag, result;

  char *hello_msg = "Hello World!\n";
  char *pass_msg = "\nTest passed :-)\n";
  char *fail_msg = "\nTest failed :-(((((\n";

  prints(hello_msg);

  fail_flag = hello_atest(0);

  if (fail_flag == 0) {
    prints(pass_msg);
  }

  return 0;
   
}

