pragma circom 2.1.5;

include "../../circuits/bitify.circom";
include "../../circuits/tags-managing.circom";



template check_components(n){

   signal input in1;
   signal output n2b[n] <== Num2Bits(n)(in1);
   signal output n2bs[254] <== Num2Bits_strict()(in1);
   
   signal input in2[n];
   signal output b2n <== Bits2Num(n)(AddBinaryArrayTag(n)(in2));
   
   signal input in3[254];
   signal output b2ns <== Bits2Num_strict()(AddBinaryArrayTag(254)(in3));
   
   
   signal output n2bn[n];
   signal output aux;
   (n2bn, aux) <== Num2BitsNeg(n)(in1);
   
}

component main = check_components(20);
