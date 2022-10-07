How to run synthesis?
===============

In order to do the synthesis of this module you need installed:
Yosys ->  http://www.clifford.at/yosys/
Verific -> http://www.clifford.at/yosys/
FreePDK45  -> https://www.eda.ncsu.edu/wiki/FreePDK45:Contents#Current_Version

Verific can be obtained for free through the sby package granted to BSC.
https://symbiyosys.readthedocs.io/en/latest/

All the paths in the .ys files containing the falg -liberty have the absolute 
path to the liberty files of the pdk that we are using. Since this paths are
hardcoded you will need to set yours manually. it shall be replaced by a system
variable in the future.

List of experiments
=======================

*FT-resource-comp: Area/resources and frequency comparison of
hamming16t11d, , reg_sbf, and com_tr fault tolerance mechanisms.
All resources are configured to protect signals/registers of
8, 11, 32 and 64 bits. FreePDK45

*PMU\_configs: Area scaling of the non fault tolerant pmu with diferent
parameters for the features. FreePDK45

*FT-PMU-comp: Area and frequency comparison between fault tolerant (FT) and non
fault tolerant (NFT) of the pmu with default configurations. FreePDK45 

