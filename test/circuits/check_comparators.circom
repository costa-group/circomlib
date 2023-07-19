pragma circom 2.1.5;

include "../../circuits/comparators.circom";
include "../../circuits/tags-managing.circom";



template check_components(n){

   signal input in1;
   signal output isz <== IsZero()(in1);
   
   signal input in2;
   signal output ise <== IsEqual()([in1, in2]);
   
   signal input fe;
   ForceEqualIfEnabled()(AddBinaryTag()(fe), [in1, in2]);

   signal input in_comp[2];
   
   signal checked_in[2] <== AddMaxbitArrayTag(n, 2)(in_comp);
   
   signal output out_lt <== LessThan(n)(checked_in);
   signal output out_le <== LessEqThan(n)(checked_in);
   signal output out_gt <== GreaterThan(n)(checked_in);
   signal output out_ge <== GreaterEqThan(n)(checked_in);
   
}

component main = check_components(20);
