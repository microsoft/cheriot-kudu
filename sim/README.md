Cheriot-Kudu simulations can be run either using compiled test code images or using direct instruction injection (DII). Please follow the steps below and note the vcs filelists and script may need to be modified to reflect your setup.

### Simulation with compiled code images 
#### Compile coremak test for RV32
1. cd tests
2. ../scripts/build_coremark_rv32.sh
   - The scripts genearates a 64-bit hex (coremark.rv32o3.vhx) file and place it in sim/run/bin and other files (.dis, .bin, .elf, etc) in sim/tests/work. 

#### Compile coremark test for CHERIoT
1. cd tests
2. ../scripts/build_coremark.sh
   - The scripts genearates a 64-bit hex (coremark.cheriot.vhx) file and place it in sim/run/bin and other files (.dis, .bin, .elf, etc) in sim/tests/work. 

#### Run VCS simulation with cheriot-kudu
1. cd run
2. use ./vcscomp to compile RTL and testbench in CHERIoT mode, or use ./vcscomp -rv32 to compile in RV32 mode
3. ./simv +TEST=testname
   - Here testname must correspond to a vhx file in sim/runbin/ directory
   - e.g., ./simv +TEST=coremark.cheriot
     
#### Run VCS simulation with cheriot-ibex 
1. cd run_ibex
2. create a symbolic link to ../run/bin
3. use ./vcsibex to compile RTL and testbench in CHERIoT mode, or use ./vcsibex32 to compile in RV32 mode
4. ./simv +TEST=testname

### Simulation with DII 
#### Generate DII input
1. Run a sail simulation with -v option and pipe the output to a file (e.g., testname.dii)
2. grep mem sail.og > testname.dii
3. Check the DII inputs to ensure no address duplication
   - e.g., sim/scripts/check_dii_inputs.py testname.dii
4. Place the testname.dii file in sim/run/bin/ drectory

### run VCS simulation
1. cd run
2. use ./vcscomp -dii to complile RTL and testbench for DII simulation
3. ./simv +TEST=testname
   - optionally use +TIMEOUT=xxx to stop simulation (default timeout is 1 million cycles)
5. Compare kudu trace vs. sail trace for correctness
