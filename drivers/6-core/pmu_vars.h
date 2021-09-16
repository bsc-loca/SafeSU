#define REG_WIDTH 32
#define N_COUNTERS 24
#define N_CONF_REGS 1
#define OVERFLOW 1
#define QUOTA 1
#define MCCU 1
#define RDC 1
#define BASE_CFG 0
#define END_CFG 0
#define BASE_COUNTERS 1
#define END_COUNTERS 24
#define BASE_OVERFLOW_INTR 25
#define BASE_OVERFLOW_MASK 25
#define N_OVERFLOW_MASK_REGS 1
#define END_OVERFLOW_MASK 25
#define BASE_OVERFLOW_VECT 26
#define N_OVERFLOW_VECT_REGS 1
#define END_OVERFLOW_VECT 26
#define N_OVERFLOW_REGS 2
#define END_OVERFLOW_INTR 26
#define BASE_QUOTA_INTR 27
#define BASE_QUOTA_MASK 27
#define N_QUOTA_MASK_REGS 1
#define END_QUOTA_MASK 27
#define BASE_QUOTA_LIMIT 28
#define N_QUOTA_LIMIT_REGS 1
#define END_QUOTA_LIMIT 28
#define N_QUOTA_REGS 2
#define END_QUOTA_INTR 28
#define MCCU_WEIGHTS_WIDTH 8
#define MCCU_N_CORES 6
#define MCCU_N_EVENTS 2
#define BASE_MCCU_CFG 29
#define N_MCCU_CFG 1
#define END_MCCU_CFG 29
#define BASE_MCCU_LIMITS 30
#define N_MCCU_LIMITS 6
#define END_MCCU_LIMITS 35
#define BASE_MCCU_QUOTA 36
#define N_MCCU_QUOTA 6
#define END_MCCU_QUOTA 41
#define BASE_MCCU_WEIGHTS 42
#define N_MCCU_WEIGHTS 3
#define END_MCCU_WEIGHTS 44
#define N_MCCU_REGS 16
#define RDC_WEIGHTS_WIDTH 8
#define RDC_N_CORES 6
#define RDC_N_EVENTS 2
#define BASE_RDC_VECT 45
#define N_RDC_VECT_REGS 1
#define END_RDC_VECT 45
#define BASE_RDC_WEIGHTS 42
#define N_RDC_WEIGHTS 0
#define END_RDC_WEIGHTS 44
#define BASE_RDC_WATERMARK 46
#define N_RDC_WATERMARK 3
#define END_RDC_WATERMARK 48
#define N_RDC_REGS 4
#define CROSSBAR_INPUTS 128
#define BASE_CROSSBAR 49
#define N_CROSSBAR_CFG 6
#define END_CROSSBAR 56
#define N_CROSSBAR_REGS 6
#define TOTAL_NREGS 55

#define _PMU_REG_TYPE(volatile unsigned int * )
#define R2A (REG_WIDTH/8)
// PMU base address
#define _PMUREG(_PMU_REG_TYPE(PMU_ADDR))
// PMU counter base address
#define _PMU_COUNTERS(_PMU_REG_TYPE(PMU_ADDR + R2A * BASE_CFG ))

// PMU crossbar base address
#define _PMU_CROSSBAR(_PMU_REG_TYPE(PMU_ADDR + R2A * BASE_CROSSBAR))

// PMU overflow interrupt register base address
#define _PMU_OVERFLOW(_PMU_REG_TYPE(PMU_ADDR + R2A * BASE_OVERFLOW_INTR))

#define PMUCFG0(_PMUREG[0]) // PMU configuration register 0
#define CROSSBAR_REG0(_PMU_CROSSBAR[0]) // Crossbar output register 0
#define CROSSBAR_REG1(_PMU_CROSSBAR[1]) // Crossbar output register 1
#define CROSSBAR_REG2(_PMU_CROSSBAR[2]) // Crossbar output register 2
#define CROSSBAR_REG3(_PMU_CROSSBAR[3]) // Crossbar output register 3
#define CROSSBAR_REG4(_PMU_CROSSBAR[4]) // Crossbar output register 4
#define CROSSBAR_REG5(_PMU_CROSSBAR[5]) // Crossbar output register 5

// PMU overflow (I)nterrupt (E)nable register 
#define PMU_OVERLFOW_IE(_PMU_OVERFLOW[0])

// PMU overflow (I)nterrupt (V)ector register
#define PMU_OVERFLOW_IV(_PMU_OVERFLOW[1])

#define CROSSBAR_OUTPUT_0(0 U)
#define CROSSBAR_OUTPUT_1(1 U)
#define CROSSBAR_OUTPUT_2(2 U)
#define CROSSBAR_OUTPUT_3(3 U)
#define CROSSBAR_OUTPUT_4(4 U)
#define CROSSBAR_OUTPUT_5(5 U)
#define CROSSBAR_OUTPUT_6(6 U)
#define CROSSBAR_OUTPUT_7(7 U)
#define CROSSBAR_OUTPUT_8(8 U)
#define CROSSBAR_OUTPUT_9(9 U)
#define CROSSBAR_OUTPUT_10(10 U)
#define CROSSBAR_OUTPUT_11(11 U)
#define CROSSBAR_OUTPUT_12(12 U)
#define CROSSBAR_OUTPUT_13(13 U)
#define CROSSBAR_OUTPUT_14(14 U)
#define CROSSBAR_OUTPUT_15(15 U)
#define CROSSBAR_OUTPUT_16(16 U)
#define CROSSBAR_OUTPUT_17(17 U)
#define CROSSBAR_OUTPUT_18(18 U)
#define CROSSBAR_OUTPUT_19(19 U)
#define CROSSBAR_OUTPUT_20(20 U)
#define CROSSBAR_OUTPUT_21(21 U)
#define CROSSBAR_OUTPUT_22(22 U)
#define CROSSBAR_OUTPUT_23(23 U)
#define CROSSBAR_OUTPUT_24(24 U)

#define EVENT_0(0 U)
#define EVENT_1(1 U)
#define EVENT_2(2 U)
#define EVENT_3(3 U)
#define EVENT_4(4 U)
#define EVENT_5(5 U)
#define EVENT_6(6 U)
#define EVENT_7(7 U)
#define EVENT_8(8 U)
#define EVENT_9(9 U)
#define EVENT_10(10 U)
#define EVENT_11(11 U)
#define EVENT_12(12 U)
#define EVENT_13(13 U)
#define EVENT_14(14 U)
#define EVENT_15(15 U)
#define EVENT_16(16 U)
#define EVENT_17(17 U)
#define EVENT_18(18 U)
#define EVENT_19(19 U)
#define EVENT_20(20 U)
#define EVENT_21(21 U)
#define EVENT_22(22 U)
#define EVENT_23(23 U)
#define EVENT_24(24 U)
#define EVENT_25(25 U)
#define EVENT_26(26 U)
#define EVENT_27(27 U)
#define EVENT_28(28 U)
#define EVENT_29(29 U)
#define EVENT_30(30 U)
#define EVENT_31(31 U)
#define EVENT_32(32 U)
#define EVENT_33(33 U)
#define EVENT_34(34 U)
#define EVENT_35(35 U)
#define EVENT_36(36 U)
#define EVENT_37(37 U)
#define EVENT_38(38 U)
#define EVENT_39(39 U)
#define EVENT_40(40 U)
#define EVENT_41(41 U)
#define EVENT_42(42 U)
#define EVENT_43(43 U)
#define EVENT_44(44 U)
#define EVENT_45(45 U)
#define EVENT_46(46 U)
#define EVENT_47(47 U)
#define EVENT_48(48 U)
#define EVENT_49(49 U)
#define EVENT_50(50 U)
#define EVENT_51(51 U)
#define EVENT_52(52 U)
#define EVENT_53(53 U)
#define EVENT_54(54 U)
#define EVENT_55(55 U)
#define EVENT_56(56 U)
#define EVENT_57(57 U)
#define EVENT_58(58 U)
#define EVENT_59(59 U)
#define EVENT_60(60 U)
#define EVENT_61(61 U)
#define EVENT_62(62 U)
#define EVENT_63(63 U)
#define EVENT_64(64 U)
#define EVENT_65(65 U)
#define EVENT_66(66 U)
#define EVENT_67(67 U)
#define EVENT_68(68 U)
#define EVENT_69(69 U)
#define EVENT_70(70 U)
#define EVENT_71(71 U)
#define EVENT_72(72 U)
#define EVENT_73(73 U)
#define EVENT_74(74 U)
#define EVENT_75(75 U)
#define EVENT_76(76 U)
#define EVENT_77(77 U)
#define EVENT_78(78 U)
#define EVENT_79(79 U)
#define EVENT_80(80 U)
#define EVENT_81(81 U)
#define EVENT_82(82 U)
#define EVENT_83(83 U)
#define EVENT_84(84 U)
#define EVENT_85(85 U)
#define EVENT_86(86 U)
#define EVENT_87(87 U)
#define EVENT_88(88 U)
#define EVENT_89(89 U)
#define EVENT_90(90 U)
#define EVENT_91(91 U)
#define EVENT_92(92 U)
#define EVENT_93(93 U)
#define EVENT_94(94 U)
#define EVENT_95(95 U)
#define EVENT_96(96 U)
#define EVENT_97(97 U)
#define EVENT_98(98 U)
#define EVENT_99(99 U)
#define EVENT_100(100 U)
#define EVENT_101(101 U)
#define EVENT_102(102 U)
#define EVENT_103(103 U)
#define EVENT_104(104 U)
#define EVENT_105(105 U)
#define EVENT_106(106 U)
#define EVENT_107(107 U)
#define EVENT_108(108 U)
#define EVENT_109(109 U)
#define EVENT_110(110 U)
#define EVENT_111(111 U)
#define EVENT_112(112 U)
#define EVENT_113(113 U)
#define EVENT_114(114 U)
#define EVENT_115(115 U)
#define EVENT_116(116 U)
#define EVENT_117(117 U)
#define EVENT_118(118 U)
#define EVENT_119(119 U)
#define EVENT_120(120 U)
#define EVENT_121(121 U)
#define EVENT_122(122 U)
#define EVENT_123(123 U)
#define EVENT_124(124 U)
#define EVENT_125(125 U)
#define EVENT_126(126 U)
#define EVENT_127(127 U)

#define _PMU_MCCU_RDC(_PMU_REG_TYPE(PMU_ADDR + R2A * BASE_MCCU_CFG))
#define _PMU_MCCU_QUOTA(_PMU_REG_TYPE(PMU_ADDR +  R2A * BASE_MCCU_LIMITS))
#define _PMU_RDC_WATERMARKS(_PMU_REG_TYPE(PMU_ADDR + R2A  BASE_RDC_WATERMARK))

#define PMUCFG1(_PMU_MCCU_RDC[0]) // PMU configuration register 1

#define PMU_QUOTA_REM0(_PMU_MCCU_QUOTA[4]) // Quota current remaining for core 0
#define PMU_QUOTA_REM1(_PMU_MCCU_QUOTA[5]) // Quota current remaining for core 1
#define PMU_QUOTA_REM2(_PMU_MCCU_QUOTA[6]) // Quota current remaining for core 2
#define PMU_QUOTA_REM3(_PMU_MCCU_QUOTA[7]) // Quota current remaining for core 3
#define PMU_QUOTA_REM4(_PMU_MCCU_QUOTA[8]) // Quota current remaining for core 4
#define PMU_QUOTA_REM5(_PMU_MCCU_QUOTA[9]) // Quota current remaining for core 5

#define EVENT_WEIGHT_REG0(_PMU_MCCU_QUOTA[8]) // Event weight register 0 (input 0 to 3)
#define EVENT_WEIGHT_REG1(_PMU_MCCU_QUOTA[9]) // Event weight register 1 (input 4 to 7)
#define EVENT_WEIGHT_REG2(_PMU_MCCU_QUOTA[10]) // Event weight register 1 (input 4 to 7)

#define _PMU_RDC_IV(_PMU_REG_TYPE(PMU_ADDR + BASE_RDC_VECT * R2A))
#define PMU_RDC_IV(_PMU_RDC_IV[0])

#define PMU_RDC_WATERMARK_REG0(_PMU_RDC_WATERMARKS[0])
#define PMU_RDC_WATERMARK_REG1(_PMU_RDC_WATERMARKS[1])

#define EV_WEIGHT_INPUT0(0 U)
#define EV_WEIGHT_INPUT1(1 U)
#define EV_WEIGHT_INPUT2(2 U)
#define EV_WEIGHT_INPUT3(3 U)
#define EV_WEIGHT_INPUT4(4 U)
#define EV_WEIGHT_INPUT5(5 U)
#define EV_WEIGHT_INPUT6(6 U)
#define EV_WEIGHT_INPUT7(7 U)

#define PMU_OVERFLOW_INT_INDEX(6 U)
