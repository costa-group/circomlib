pragma circom 2.1.5;

include "./poseidon_constants.circom";
include "./poseidon_utils.circom";
include "tags-specifications.circom";


// To consult the tags specifications check tags-specifications.circom

/*

*** MixLast(t, M, s): template that receives an input array of signals in of length t, and returns a field value out such that out = Sum_{j = 0, ..., t-1} (M[j][s] * in[j])
        - Inputs: in[t] -> field value
        - Outputs: out -> field value
        
    MixLast(2, [[1, 2], [3, 4]], 1)([1, 0]) = 3
    
    Obs: M is expected to be a matrix of dimensions at leadt t * t, s is a value between 0..t-1
    
*/

template MixLast(t, M, s) {
    signal input in[t];
    signal output out;

    var lc = 0;
    for (var j=0; j<t; j++) {
        lc += M[j][s]*in[j];
    }
    out <== lc;
}


/*

*** MixS(t, M, r): template that receives an input array of signals in of length t, and returns the array out of length t such that
      out[0] = Sum_{i = 0, ... , t-1} (S[(t*2 - 1) * r + i] * in[i])
      out[i] = in[i] +  in[0] * S[(t*2 - 1) * r + t + i - 1]
        - Inputs: in[t] -> field value
        - Outputs: out -> field value
*/

template MixS(t, S, r) {
    signal input in[t];
    signal output out[t];


    var lc = 0;
    for (var i=0; i<t; i++) {
        lc += S[(t*2-1)*r+i]*in[i];
    }
    out[0] <== lc;
    for (var i=1; i<t; i++) {
        out[i] <== in[i] +  in[0] * S[(t*2-1)*r + t + i -1];
    }
}



/*

*** PoseidonEx(nInputs, nOuts): template that implements the Poseidon hash protocol for nInputs and nOuts. The circuit receives the inputs to be hashed, the initial state and returns the hashed values
        - Inputs: inputs[nInputs] -> field value
                  initialState -> field value
        - Outputs: out[nOuts] -> field value
*/

template PoseidonEx(nInputs, nOuts) {
    signal input inputs[nInputs];
    signal input initialState;
    signal output out[nOuts];
    
    assert(-1 == 21888242871839275222246405745257275088548364400416034343698204186575808495616);


    // Using recommended parameters from whitepaper https://eprint.iacr.org/2019/458.pdf (table 2, table 8)
    // Generated by https://extgit.iaik.tugraz.at/krypto/hadeshash/-/blob/master/code/calc_round_numbers.py
    // And rounded up to nearest integer that divides by t
    var N_ROUNDS_P[16] = [56, 57, 56, 60, 60, 63, 64, 63, 60, 66, 60, 65, 70, 60, 64, 68];
    var t = nInputs + 1;
    var nRoundsF = 8;
    var nRoundsP = N_ROUNDS_P[t - 2];
    var C[t*nRoundsF + nRoundsP] = POSEIDON_C(t);
    var S[  N_ROUNDS_P[t-2]  *  (t*2-1)  ]  = POSEIDON_S(t);
    var M[t][t] = POSEIDON_M(t);
    var P[t][t] = POSEIDON_P(t);

    component ark[nRoundsF];
    component sigmaF[nRoundsF][t];
    component sigmaP[nRoundsP];
    component mix[nRoundsF-1];
    component mixS[nRoundsP];
    component mixLast[nOuts];


    ark[0] = Ark(t, C, 0);
    for (var j=0; j<t; j++) {
        if (j>0) {
            ark[0].in[j] <== inputs[j-1];
        } else {
            ark[0].in[j] <== initialState;
        }
    }

    for (var r = 0; r < nRoundsF\2-1; r++) {
        for (var j=0; j<t; j++) {
            sigmaF[r][j] = Sigma();
            if(r==0) {
                sigmaF[r][j].in <== ark[0].out[j];
            } else {
                sigmaF[r][j].in <== mix[r-1].out[j];
            }
        }

        ark[r+1] = Ark(t, C, (r+1)*t);
        for (var j=0; j<t; j++) {
            ark[r+1].in[j] <== sigmaF[r][j].out;
        }

        mix[r] = Mix(t,M);
        mix[r].in <== ark[r+1].out;
        

    }

    for (var j=0; j<t; j++) {
        sigmaF[nRoundsF\2-1][j] = Sigma();
        sigmaF[nRoundsF\2-1][j].in <== mix[nRoundsF\2-2].out[j];
    }

    ark[nRoundsF\2] = Ark(t, C, (nRoundsF\2)*t );
    for (var j=0; j<t; j++) {
        ark[nRoundsF\2].in[j] <== sigmaF[nRoundsF\2-1][j].out;
    }

    mix[nRoundsF\2-1] = Mix(t,P);
    mix[nRoundsF\2-1].in <== ark[nRoundsF\2].out;


    for (var r = 0; r < nRoundsP; r++) {
        sigmaP[r] = Sigma();
        if (r==0) {
            sigmaP[r].in <== mix[nRoundsF\2-1].out[0];
        } else {
            sigmaP[r].in <== mixS[r-1].out[0];
        }

        mixS[r] = MixS(t, S, r);
        for (var j=0; j<t; j++) {
            if (j==0) {
                mixS[r].in[j] <== sigmaP[r].out + C[(nRoundsF\2+1)*t + r];
            } else {
                if (r==0) {
                    mixS[r].in[j] <== mix[nRoundsF\2-1].out[j];
                } else {
                    mixS[r].in[j] <== mixS[r-1].out[j];
                }
            }
        }
    }

    for (var r = 0; r < nRoundsF\2-1; r++) {
        for (var j=0; j<t; j++) {
            sigmaF[nRoundsF\2 + r][j] = Sigma();
            if (r==0) {
                sigmaF[nRoundsF\2 + r][j].in <== mixS[nRoundsP-1].out[j];
            } else {
                sigmaF[nRoundsF\2 + r][j].in <== mix[nRoundsF\2+r-1].out[j];
            }
        }

        ark[ nRoundsF\2 + r + 1] = Ark(t, C,  (nRoundsF\2+1)*t + nRoundsP + r*t );
        for (var j=0; j<t; j++) {
            ark[nRoundsF\2 + r + 1].in[j] <== sigmaF[nRoundsF\2 + r][j].out;
        }

        mix[nRoundsF\2 + r] = Mix(t,M);
        mix[nRoundsF\2 + r].in <== ark[nRoundsF\2 + r + 1].out;

    }

    for (var j=0; j<t; j++) {
        sigmaF[nRoundsF-1][j] = Sigma();
        sigmaF[nRoundsF-1][j].in <== mix[nRoundsF-2].out[j];
    }

    for (var i=0; i<nOuts; i++) {
        mixLast[i] = MixLast(t,M,i);
        for (var j=0; j<t; j++) {
            mixLast[i].in[j] <== sigmaF[nRoundsF-1][j].out;
        }
        out[i] <== mixLast[i].out;
    }

}

/*

*** Poseidon(nInputs): template that implements the Poseidon hash protocol for nInputs. The circuit receives the inputs to be hashed and returns the hashed values. It takes the value 0 as initial state. 
        - Inputs: inputs[nInputs] -> field value
        - Outputs: out -> field value
*/

template Poseidon(nInputs) {
    signal input inputs[nInputs];
    signal output out;
    
    assert(-1 == 21888242871839275222246405745257275088548364400416034343698204186575808495616);


    component pEx = PoseidonEx(nInputs, 1);
    pEx.initialState <== 0;
    pEx.inputs <== inputs;
    out <== pEx.out[0];
}
