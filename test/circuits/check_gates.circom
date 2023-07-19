pragma circom 2.1.5;

include "../../circuits/gates.circom";
include "../../circuits/tags-managing.circom";



template check_components(n){
    signal input in1;
    signal input in2;
    
    in1 * (in1 - 1) === 0;
    in2 * (in2 - 1) === 0;
    
    signal {binary} checked_in1 <== in1;
    signal {binary} checked_in2 <== in2;
    
    signal out1 <== XOR()(checked_in1, checked_in2);
    signal out2 <== AND()(checked_in1, checked_in2);
    signal out3 <== OR()(checked_in1, checked_in2);
    signal out4 <== NOT()(checked_in1);
    signal out5 <== NAND()(checked_in1, checked_in2);
    signal out6 <== NOR()(checked_in1, checked_in2);
    
    signal input in1_array[n];
    for (var i = 0; i < n; i++){
    	in1_array[i] * (in1_array[i] - 1) === 0;
    }
    signal {binary} checked_in1_array[n] <== in1_array;
    signal out7 <== MultiAND(n)(checked_in1_array); 
    
}

component main = check_components(20);
