/*
    Copyright 2018 0KIMS association.

    This file is part of circom (Zero Knowledge Circuit Compiler).

    circom is a free software: you can redistribute it and/or modify it
    under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    circom is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public
    License for more details.

    You should have received a copy of the GNU General Public License
    along with circom. If not, see <https://www.gnu.org/licenses/>.
*/
pragma circom 2.0.0;

template MultiMux4(n) {
    signal input c[n][16];  // Constants
    signal input {binary} s[4];   // Selector
    signal output out[n];

    signal a3210[n];
    signal a321[n];
    signal a320[n];
    signal a310[n];
    signal a32[n];
    signal a31[n];
    signal a30[n];
    signal a3[n];

    signal a210[n];
    signal a21[n];
    signal a20[n];
    signal a10[n];
    signal a2[n];
    signal a1[n];
    signal a0[n];
    signal a[n];

    // 4 constrains for the intermediary variables
    signal  s10;
    s10 <== s[1] * s[0];
    signal  s20;
    s20 <== s[2] * s[0];
    signal  s21;
    s21 <== s[2] * s[1];
    signal s210;
    s210 <==  s21 * s[0];
    
    spec_precondition (s[0] == 0 || s[1] == 0) => s10 == 0;
    spec_precondition (s[0] == 0 || s[2] == 0) => s20 == 0;
    spec_precondition (s[2] == 0 || s[1] == 0) => s21 == 0;
    spec_precondition (s[0] == 0 || s[1] == 0|| s[2] == 0) => s210 == 0;


    for (var i=0; i<n; i++) {

        a3210[i] <==  ( c[i][15]-c[i][14]-c[i][13]+c[i][12] - c[i][11]+c[i][10]+c[i][ 9]-c[i][ 8]
                       -c[i][ 7]+c[i][ 6]+c[i][ 5]-c[i][ 4] + c[i][ 3]-c[i][ 2]-c[i][ 1]+c[i][ 0] ) * s210;
         a321[i] <==  ( c[i][14]-c[i][12]-c[i][10]+c[i][ 8] - c[i][ 6]+c[i][ 4]+c[i][ 2]-c[i][ 0] ) * s21;
         a320[i] <==  ( c[i][13]-c[i][12]-c[i][ 9]+c[i][ 8] - c[i][ 5]+c[i][ 4]+c[i][ 1]-c[i][ 0] ) * s20;
         a310[i] <==  ( c[i][11]-c[i][10]-c[i][ 9]+c[i][ 8] - c[i][ 3]+c[i][ 2]+c[i][ 1]-c[i][ 0] ) * s10;
          a32[i] <==  ( c[i][12]-c[i][ 8]-c[i][ 4]+c[i][ 0] ) * s[2];
          a31[i] <==  ( c[i][10]-c[i][ 8]-c[i][ 2]+c[i][ 0] ) * s[1];
          a30[i] <==  ( c[i][ 9]-c[i][ 8]-c[i][ 1]+c[i][ 0] ) * s[0];
           a3[i] <==  ( c[i][ 8]-c[i][ 0] );

         a210[i] <==  ( c[i][ 7]-c[i][ 6]-c[i][ 5]+c[i][ 4] - c[i][ 3]+c[i][ 2]+c[i][ 1]-c[i][ 0] ) * s210;
          a21[i] <==  ( c[i][ 6]-c[i][ 4]-c[i][ 2]+c[i][ 0] ) * s21;
          a20[i] <==  ( c[i][ 5]-c[i][ 4]-c[i][ 1]+c[i][ 0] ) * s20;
          a10[i] <==  ( c[i][ 3]-c[i][ 2]-c[i][ 1]+c[i][ 0] ) * s10;
           a2[i] <==  ( c[i][ 4]-c[i][ 0] ) * s[2];
           a1[i] <==  ( c[i][ 2]-c[i][ 0] ) * s[1];
           a0[i] <==  ( c[i][ 1]-c[i][ 0] ) * s[0];
            a[i] <==  ( c[i][ 0] );
          
       

          
          out[i] <== ( a3210[i] + a321[i] + a320[i] + a310[i] + a32[i] + a31[i] + a30[i] + a3[i] ) * s[3] +
                     (  a210[i] +  a21[i] +  a20[i] +  a10[i] +  a2[i] +  a1[i] +  a0[i] +  a[i] );
                   
    }
    
    // specification
    
    var value_s = s[0] + 2 * s[1] + 4 * s[2] + 8 * s[3];
    
    for (var i = 0; i <n; i++){
            
    for (var i = 0; i <n; i++){
        spec_postcondition ((s[0] == 0 && s[1] == 0 && s[2] == 0 && s[3] == 0)) => (out[i] == c[i][0]);
        spec_postcondition ((s[0] == 1 && s[1] == 0 && s[2] == 0 && s[3] == 0)) => (out[i] == c[i][1]);
        spec_postcondition ((s[0] == 0 && s[1] == 1 && s[2] == 0 && s[3] == 0)) => (out[i] == c[i][2]);
        spec_postcondition ((s[0] == 1 && s[1] == 1 && s[2] == 0 && s[3] == 0)) => (out[i] == c[i][3]);
        spec_postcondition ((s[0] == 0 && s[1] == 0 && s[2] == 1 && s[3] == 0)) => (out[i] == c[i][4]);
        spec_postcondition ((s[0] == 1 && s[1] == 0 && s[2] == 1 && s[3] == 0)) => (out[i] == c[i][5]);
        spec_postcondition ((s[0] == 0 && s[1] == 1 && s[2] == 1 && s[3] == 0)) => (out[i] == c[i][6]);
        spec_postcondition ((s[0] == 1 && s[1] == 1 && s[2] == 1 && s[3] == 0)) => (out[i] == c[i][7]);
        
        spec_postcondition ((s[0] == 0 && s[1] == 0 && s[2] == 0 && s[3] == 1)) => (out[i] == c[i][8]);
        
        spec_postcondition ((s[0] == 1 && s[1] == 0 && s[2] == 0 && s[3] == 1)) => (out[i] == c[i][9]);
        
        spec_postcondition ((s[0] == 0 && s[1] == 1 && s[2] == 0 && s[3] == 1)) => (out[i] == c[i][10]);
        spec_postcondition ((s[0] == 1 && s[1] == 1 && s[2] == 0 && s[3] == 1)) => (out[i] == c[i][11]);
        spec_postcondition ((s[0] == 0 && s[1] == 0 && s[2] == 1 && s[3] == 1)) => (out[i] == c[i][12]);
        spec_postcondition ((s[0] == 1 && s[1] == 0 && s[2] == 1 && s[3] == 1)) => (out[i] == c[i][13]);
        spec_postcondition ((s[0] == 0 && s[1] == 1 && s[2] == 1 && s[3] == 1)) => (out[i] == c[i][14]);
        spec_postcondition ((s[0] == 1 && s[1] == 1 && s[2] == 1 && s[3] == 1)) => (out[i] == c[i][15]);
        

    }
    }
}

template Mux4() {
    var i;
    signal input c[16];  // Constants
    signal input {binary} s[4];   // Selector
    signal output out;

    component mux = MultiMux4(1);

    for (i=0; i<16; i++) {
        mux.c[0][i] <== c[i];
    }

    for (i=0; i<4; i++) {
      s[i] ==> mux.s[i];
    }

    mux.out[0] ==> out;
    
    // specification
    
    var value_s = s[0] + 2 * s[1] + 4 * s[2] + 8 * s[3];
    
    spec_postcondition ((value_s == 0)) => (out == c[0]);
    spec_postcondition ((value_s == 1)) => (out == c[1]);
    spec_postcondition ((value_s == 2)) => (out == c[2]);
    spec_postcondition ((value_s == 3)) => (out == c[3]);
    spec_postcondition ((value_s == 4)) => (out == c[4]);
    spec_postcondition ((value_s == 5)) => (out == c[5]);
    spec_postcondition ((value_s == 6)) => (out == c[6]);
    spec_postcondition ((value_s == 7)) => (out == c[7]);
    spec_postcondition ((value_s == 8)) => (out == c[8]);
    spec_postcondition ((value_s == 9)) => (out == c[9]);
    spec_postcondition ((value_s == 10)) => (out == c[10]);
    spec_postcondition ((value_s == 11)) => (out == c[11]);
    spec_postcondition ((value_s == 12)) => (out == c[12]);
    spec_postcondition ((value_s == 13)) => (out == c[13]);
    spec_postcondition ((value_s == 14)) => (out == c[14]);
    spec_postcondition ((value_s == 15)) => (out == c[15]);
}
