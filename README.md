# Safe Statistics Unit (SafeSU)

The Safe Statistics Unit (SafeSU for short) is an RTL IP that implements several mechanisms for multicore timing interference verification, validation, and monitoring. It has been integrated into commercial space-graded RISC-V and SparcV8 MPSoCs.

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


## Repo organization
This repository contains the RTL and documentation for the unit. 


*  The specs for each feature and memory map calculator can be found under the ```docs``` folder.
*  Top levels for different configurations or wrappers are found in ```rtl```.
*  RTL for Submodules (MCCU, RDC, Counters, etc..) can be found in ```submodules```.
*  Synth contains scripts for early area and frequency evaluation with yosys.
*  ```tb``` contains testbenches, verification scripts and example of software codes inside ```software_tests```.
*  Drivers or APIs can be found inside the ```drivers```.
* Davos injection tool has been also added inside ```tools```.
