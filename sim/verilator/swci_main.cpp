#include <stdlib.h>
#include <fcntl.h>
#include <iostream>
#include <verilated.h>
//#include <verilated_vcd_c.h>
#include "Vtb_kudu_top.h"
#include "Vtb_kudu_top___024root.h"

#define MAX_SIM_TIME 2000000000        // 100M cycles
// #define VCD_TRACE
vluint64_t sim_time = 0;

int main(int argc, char** argv, char** env) {
    unsigned char exit_flag, exit_code;

    Verilated::commandArgs(argc, argv);
    VerilatedContext *contextp = new VerilatedContext;
    contextp->commandArgs(argc, argv);

    Vtb_kudu_top *dut = new Vtb_kudu_top;

    // Verilated::traceEverOn(true);
    // VerilatedVcdC *m_trace = new VerilatedVcdC;
    uint64_t sim_time = 0;

    //dut->rstn_i = 1;


    while (!Verilated::gotFinish()) {
        //dut->sysclk_i ^= 1;
        dut->eval();
        contextp->timeInc(1);
        sim_time++;
    }

    delete dut;

    printf ("Exiting simulation.. \n");
    exit(exit_code);
}
