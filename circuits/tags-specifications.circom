/*

Used tags:

*** binary: is a tag without value that indicates that the signal should have a binary value (0 or 1);
        Formally: if x has tag binary then x*(x-1) === 0 is expected to be true
	(although it's not checked by the compiler)

*** maxbit: is a tag with value that indicates maximum number of bits needed to represent the signal value;
        Formally: if x has tag maxbit with value m then there should exist x_0...x_{m-1} with x_i*(x_i-1) === 0 s.t.
        x = sum_{i=0}^{n-1} x_i * 2**i (although it's not checked by the compiler)
        
*** max: is a tag with value that indicates the maximum value that a signal can take;
        Formally: if x has tag max with value m then 0 <= x <= m is expected to be true
        (although it's not checked by the compiler)
        
*** max_abs: is a tag with value that indicates the maximum absolute value that a signal can take (we consider the numbers in (p\2, p-1] as negative)
        Formally: if x has tag max_abs with value m then -m <= val(x) <= m with val(x) = x if x <= p\2, val(x) = p - x if x > p\2
        (although it's not checked by the compiler) 

In all these templates if the inputs fulfil the conditions associated to their tags then
the outputs fulfil the conditions associated to their tags


*/
