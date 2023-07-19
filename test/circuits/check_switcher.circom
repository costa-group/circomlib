pragma circom 2.1.5;

include "../../circuits/switcher.circom";
include "../../circuits/tags-managing.circom";



template check_components(){

   signal input in1, in2, in3;
   
   signal output out1, out2;
   
   (out1, out2) <== Switcher()(AddBinaryTag()(in1), in2, in3);
   
}

component main = check_components();
