pragma circom 2.1.5;

include "tags-specifications.circom";


// To consult the tags specifications check tags-specifications.circom

/*

*** Sigma(): template that receives an input in an returns the value in ** 5:
        - Inputs: in -> field value
        - Outputs: out -> field value
   
   Example: Sigma()(2) = 32  
 */
 
template Sigma() {
    signal input in;
    signal output out;

    signal in2;
    signal in4;

    in2 <== in*in;
    in4 <== in2*in2;

    out <== in4*in;
}



/*

*** Ark(t, C, r): template that receives an input array of signals in of length t, and returns the array out of length t such that for each position of the array out[i] = in[i] + C[i+r] with C and r parameters of the template (r is the shifting to be used and C the values to be added) 
        - Inputs: in[t] -> field value
        - Outputs: out[t] -> field value
        
    Ark(2, [1, 2, 3, 4], 2)([5, 5]) = [8, 9]
    
    Obs: C is expected to be an array of length at least t + r
    
*/

template Ark(t, C, r) {
    signal input in[t];
    signal output out[t];

    for (var i=0; i<t; i++) {
        out[i] <== in[i] + C[i + r];
    }
}


/*

*** Mix(t, M): template that receives an input array of signals in of length t, and returns the array out of length t such that out[i] = Sum_{j = 0, ..., t-1} (M[j][i] * in[j])
        - Inputs: in[t] -> field value
        - Outputs: out[t] -> field value
        
    Mix(2, [[1, 2], [3, 4]])([1, 0]) = [1, 3]
    
    Obs: M is expected to be a matrix of dimensions at leadt t * t
    
*/

template Mix(t, M) {
    signal input in[t];
    signal output out[t];

    var lc;
    for (var i=0; i<t; i++) {
        lc = 0;
        for (var j=0; j<t; j++) {
            lc += M[j][i]*in[j];
        }
        out[i] <== lc;
    }
}

