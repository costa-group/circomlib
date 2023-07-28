pragma circom 2.0.0;

include "../../circuits/mux3.circom";
include "../../circuits/bitify.circom";


template Constants() {
    var i;
    signal output out[8];

    out[0] <== 37;
    out[1] <== 47;
    out[2] <== 53;
    out[3] <== 71;
    out[4] <== 89;
    out[5] <== 107;
    out[6] <== 163;
    out[7] <== 191;
    
        spec_postcondition out[0] == 37;
    spec_postcondition out[1] == 47;
    spec_postcondition out[2] == 53;
    spec_postcondition out[3] == 71;
    spec_postcondition out[4] == 89;
    spec_postcondition out[5] == 107;
    spec_postcondition out[6] == 163;
    spec_postcondition out[7] == 191;
}

template Main() {
    var i;
    signal input selector;//private
    signal output out;

    component mux = Mux3();
    component n2b = Num2Bits(3);
    component cst = Constants();

    selector ==> n2b.in;
    for (i=0; i<3; i++) {
        n2b.out[i] ==> mux.s[i];
    }
    for (i=0; i<8; i++) {
        cst.out[i] ==> mux.c[i];
    }

    mux.out ==> out;
    
    spec_postcondition (selector == 0) => (out == 37); 
    spec_postcondition (selector == 1) => (out == 47); 
    spec_postcondition (selector == 2) => (out == 53); 
    spec_postcondition (selector == 3) => (out == 71); 
    spec_postcondition (selector == 4) => (out == 89); 
    spec_postcondition (selector == 5) => (out == 107); 
    spec_postcondition (selector == 6) => (out == 163); 
    spec_postcondition (selector == 7) => (out == 191); 
    spec_postcondition (0 <= selector) && (selector <= 7);
}

component main = Main();
