IPs for Transient and permanent error detection and correction mechanisms

* com\_tr.sv: Single or multiple event transient error detector for
  combinational logic. Registered output error signal. Non-intrusive changes. 
* reg\_sbf.sv: Single bitflip error detection for registers. Registered output
   signal. Non-intrusive changes.
* ecc\_reg\_sbf.sv: Single bitflip error correction for registers.
* hamming16t11d\_enc: SEC-DEC Hamming encoder. 11 data bits, 5 check bits.
* hamming16t11d\_dec: SEC-DEC Hamming decoder. 11 data bits, 5 check bits.
* way3\_voter: Tree way voter for replicated logic.

