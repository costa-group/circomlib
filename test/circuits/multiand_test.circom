pragma circom 2.0.0;

include "../../circuits/comparators.circom";
include "../../circuits/bitify.circom";
include "../../circuits/gates.circom";


template A(n){
    signal input in1;
    
    component n2b1 = Num2Bits(n);
    
    n2b1.in <== in1;
    
    signal b1[n] <== n2b1.out;
    
    component ma = MultiAND(n);
    ma.in <== b1;
    
    
    component isz = IsEqual();
    isz.in[0] <== in1;
    isz.in[1] <== 2**n - 1;
    
    isz.out === ma.out;



}

component main = A(30);
