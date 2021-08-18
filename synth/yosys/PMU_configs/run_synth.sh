#Name of the report follows this format
# Q: Quota on
# O: Overflow on
# M: MCCU on
# NC: Number of counters
# NCFG: Number configuration registers
# C: Number of cores
echo "Starting synth in parallel of  the different test cases"
echo "This use to take between 1 and 3 minutes"
echo "Area for FreePDK45 is reported in square micrometers"
echo "0/8 runs done"

#`ifdef YOSYS_1
#    localparam integer N_COUNTERS	= 19;
#    // Configuration registers
#    localparam integer N_CONF_REGS	= 5;
#    localparam N_CORES = 1;
#    localparam OVERFLOW = 1;
#    localparam QUOTA= 1;
#    localparam MCCU= 1;
yosys -D YOSYS_1 yosys_45.ys > ./logs/QOM_NC19-NCFG5-C1.log &

#`elsif YOSYS_2
#    localparam integer N_COUNTERS	= 19;
#    // Configuration registers
#    localparam integer N_CONF_REGS	= 5;
#    localparam N_CORES = 2;
#    localparam OVERFLOW = 1;
#    localparam QUOTA= 1;
#    localparam MCCU= 1;
yosys -D YOSYS_2 yosys_45.ys > ./logs/QOM_NC19-NCFG5-C2.log &
#`elsif YOSYS_3
#    localparam integer N_COUNTERS	= 19;
#    // Configuration registers
#    localparam integer N_CONF_REGS	= 5;
#    localparam N_CORES = 3;
#    localparam OVERFLOW = 1;
#    localparam QUOTA= 1;
#    localparam MCCU= 1;
yosys -D YOSYS_3 yosys_45.ys > ./logs/QOM_NC19-NCFG5-C3.log &
#`elsif YOSYS_4
#    localparam integer N_COUNTERS	= 19;
#    // Configuration registers
#    localparam integer N_CONF_REGS	= 5;
#    localparam N_CORES = 4;
#    localparam OVERFLOW = 1;
#    localparam QUOTA= 1;
#    localparam MCCU= 1;
yosys -D YOSYS_4 yosys_45.ys > ./logs/QOM_NC19-NCFG5-C4.log
echo "4/8 runs done"
#`elsif YOSYS_5
#    localparam integer N_COUNTERS	= 19;
#    // Configuration registers
#    localparam integer N_CONF_REGS	= 5;
#    localparam N_CORES = 1;
#    localparam OVERFLOW = 0;
#    localparam QUOTA= 0;
#    localparam MCCU= 0;
yosys -D YOSYS_5 yosys_45.ys > ./logs/NC19-NCFG5-C1.log &
#`elsif YOSYS_6
#    localparam integer N_COUNTERS	= 19;
#    // Configuration registers
#    localparam integer N_CONF_REGS	= 5;
#    localparam N_CORES = 1;
#    localparam OVERFLOW = 1;
#    localparam QUOTA= 0;
#    localparam MCCU= 0;
yosys -D YOSYS_6 yosys_45.ys > ./logs/O_NC19-NCFG5-C1.log &
#`elsif YOSYS_7
#    localparam integer N_COUNTERS	= 19;
#    // Configuration registers
#    localparam integer N_CONF_REGS	= 5;
#    localparam N_CORES = 1;
#    localparam OVERFLOW = 0;
#    localparam QUOTA= 1;
#    localparam MCCU= 0;
yosys -D YOSYS_7 yosys_45.ys > ./logs/Q_NC19-NCFG5-C1.log &
#`elsif YOSYS_8
#    localparam integer N_COUNTERS	= 19;
#    // Configuration registers
#    localparam integer N_CONF_REGS	= 5;
#    localparam N_CORES = 1;
#    localparam OVERFLOW = 0;
#    localparam QUOTA= 0;
#    localparam MCCU= 1;
yosys -D YOSYS_8 yosys_45.ys > ./logs/M_NC19-NCFG5-C1.log
wait
echo "8/8 runs done"
echo "Done! Reporting area & cycle time"
cd logs
ack "Chip area for top module "
ack "Delay "
cd ..
