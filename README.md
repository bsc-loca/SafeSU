# Safe Statistics Unit (SafeSU)

The Safe Statistics Unit (SafeSU for short) is an RTL IP that implements several mechanisms for multicore timing interference verification, validation, and monitoring. It has been integrated into commercial space-graded RISC-V and SparcV8 MPSoCs.

### Branch: `ft/throughput_quota`

This branch introduces a customized secondary Memory Controller Counter Unit (MCCU) designed specifically for quota-based monitoring of accelerator workloads. It tracks the cumulative transfer size (in bytes) and triggers an interrupt signal whenever the assigned quota is exhausted.

#### Motivation
The original MCCU was designed to monitor CPU-event accesses using two input events and their respective weights. However, this approach is inadequate for accelerator traffic due to the increased variety of transfer types (e.g., variable access sizes, wrap/fixed modes). Extending the original MCCU to support these complex accelerator features would incur massive implementation overhead, potentially exhausting the memory allocation for the SafeSU module.

#### Implementation Details
To solve this without the overhead, a secondary MCCU has been implemented specifically for monitoring accelerator events. 

Located in `hdl/PMU_raw.sv`, the hardware implementation features:
* **Three independent MCCU quotas:** Configured primarily to monitor `READ`, `WRITE`, and `READ+WRITE` cumulative traffic sizes.
* **Low-footprint architecture:** Each quota uses dedicated wiring to connect 16 input events to 6 weights. These weights are shared in a specific configuration to minimize the hardware footprint.

#### Prerequisites & Workflow
Because of this highly optimized, low-footprint design, the hardware must be rewired to tailor it to different accelerator traffic behaviors. **A profiling step of the accelerator traffic is compulsory prior to wiring the SafeSU secondary MCCU.**

To deploy this module, follow this workflow:
1. **Profile the Traffic:** Identify the specific events that need to be monitored by the accelerator.
2. **Hardware Wiring:** Use the event profile to set the hardware links between the input events and the weights.
3. **Software Configuration:** Configure the actual weight values via software to ensure precise monitoring of the accelerator's total transfer size.

## Repo organization
This repository contains the RTL and documentation for the unit. 


*  The specs for each feature and memory map calculator can be found under the ```docs``` folder.
*  Top levels for different configurations or wrappers are found in ```rtl```.
*  RTL for Submodules (MCCU, RDC, Counters, etc..) can be found in ```submodules```.
*  Synth contains scripts for early area and frequency evaluation with yosys.
*  ```tb``` contains testbenches, verification scripts and example of software codes inside ```software_tests```.
*  Drivers or APIs can be found inside the ```drivers```.
* Davos injection tool has been also added inside ```tools```.


## Reference

If you are using the SafeSU IP for an academic publication, please cite the following paper:

G. Cabo et al., "SafeSU: an Extended Statistics Unit for Multicore Timing Interference," 2021 IEEE European Test Symposium (ETS), 2021, pp. 1-4, doi: 10.1109/ETS50041.2021.9465444

```
@INPROCEEDINGS{9465444,
  author={Cabo, Guillem and Bas, Francisco and Lorenzo, Ruben and Trilla, David and Alcaide, Sergi and Moretó, Miquel and Hernández, Carles and Abella, Jaume},
  booktitle={2021 IEEE European Test Symposium (ETS)}, 
  title={SafeSU: an Extended Statistics Unit for Multicore Timing Interference}, 
  year={2021},
  pages={1-4},
  doi={10.1109/ETS50041.2021.9465444}}
```

If you use the Safety Features please also cite the following paper:


G. Cabo et al., "SafeSU-2: a Safe Statistics Unit for Space MPSoCs," 2022 Design, Automation & Test in Europe Conference & Exhibition (DATE), 2022, pp. 1085-1086, doi: 10.23919/DATE54114.2022.9774515.

```
@INPROCEEDINGS{9774515,
  author={Cabo, Guillem and Alcaide, Sergi and Hernández, Carles and Benedicte, Pedro and Bas, Francisco and Mazzocchetti, Fabio and Abella, Jaume},
  booktitle={2022 Design, Automation & Test in Europe Conference & Exhibition (DATE)}, 
  title={SafeSU-2: a Safe Statistics Unit for Space MPSoCs}, 
  year={2022},
  volume={},
  number={},
  pages={1085-1086},
  doi={10.23919/DATE54114.2022.9774515}}
```
