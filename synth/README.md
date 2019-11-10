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
