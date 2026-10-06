#include <util.h>

// Should not be inlined, because we expect arguments
// in particular registers.
//__attribute__((noinline))

extern int cheri_atest(int);

unsigned int temp_array[16];
volatile unsigned char *ptr1;

int mymain () {
  int fail_flag, result;
  int i, j;
  unsigned int tint1, tint2;
  unsigned short ts1, ts2;

  char *hello_msg = "Running ISA test 2!\n";
  char *unaligned_msg = "Testing unaligned load/stores..\n";
  char *pass_msg = "\nTest passed :-)\n";
  char *fail_msg = "\nTest failed :-(((((\n";

  prints(hello_msg);

  fail_flag = 0;

  result = cheri_atest(0);
  if (result != 0) {
    prints(fail_msg);
    fail_flag += result;
    return -1;
  }

  if (fail_flag == 0) {
    prints(pass_msg);
  }

  return 0;
   
}

