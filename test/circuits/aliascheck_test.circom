pragma circom 2.0.0;
include "../../circuits/aliascheck.circom";
include "../../circuits/tags-managing.circom";


template Main(){
    signal input in[maxbits()+1];
    
    component cb = AddBinaryArrayTag(maxbits()+1);
    cb.in <== in;
    
    component ac = AliasCheck();
    ac.in <== cb.out;


}

component main = Main();
