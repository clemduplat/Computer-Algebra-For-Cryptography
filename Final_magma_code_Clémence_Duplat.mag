//Clémence Duplat r0977801
clear;
//------------------Task 1----------------//
function root_calculation(field,pol)
    // Here, we will try to find the roots of my polynomial (pol) in the finite field (field)
    // It follow the root finding algorithm (witrh partial factorisation) described in the slides
    // field is X or Y and pol is f or g in our case based on if you want (Inverse)Isomorphism
    R<z> := PolynomialRing(field);
    //n := Degree(pol);
    if Degree(pol) eq 0 then 
        // we know that if n equal 0, we have no roots because it is a cst term
        return [];
    elif Degree(pol) eq 1 then 
        //return the roots in the field
        return [z-pol]; 
    end if;
    q := #field;
    field_quo<y> := quo<R |pol>; //R[z]/pol field extension where the pol is assumed to be minimal of a root
    // compute the gcd(h=gcd(x^q-x),f(x)) using repeated squaring in F_q[x]/(f(X))
    // If h =1, then f has no roots in F_q
    // Otherwise: call Cantor-Zassenhaus on h to find gactors x-u_i for i =1,...,deg(h) with u_i the roots of f over F_q
    stop := true;
    while stop eq true do 
        // build a new polynomial of random degree by randomly selcting coeffiencients -> explore all directions
        // but degree less than initial 
        alpha := R !0 ;
        for i in [0..Random(1,Degree(pol)-1)] do
            alpha +:= Random(field)*z^i;
        end for;
        //compute the GCD to see if the random polynomial and the polynomial have a common factor
        r := GCD(pol,alpha);
        // if it is not equal to 1 (non-trivial common factor), we will recursively calculat roots of this common factor and pol/factor that will split or pol in simpler factors
        if r ne 1 then return root_calculation(field, r) cat root_calculation(field, ExactQuotient(pol, r)); stop := false; end if;
        // change of field to exploit the field properties
        // we use the properties of the fields for factorizations and Fermat's Little Theorem
        beta := R ! ((field_quo!alpha)^((q-1) div 2));
        // helps to isolate factors of pol that correspond to roots for which alpha is a non-residue -> refin the search fro roots by separting pol
        r_2 := GCD(beta-1,pol);
        if r_2 ne pol and r_2 ne 1 then return root_calculation(field, r_2) cat root_calculation(field, ExactQuotient(pol, r_2)); stop := false; end if;
    end while;
end function;
function FieldIsomorphism(f, g)
    p := Characteristic(BaseRing(Parent(f)));
    Fp := GF(p);
    Y<y> := ext<Fp | g>;
    R<z> := PolynomialRing(Fp);
    n := Degree(f);
    // all the roots of f in Y
    roots := root_calculation(Y,f);
    if #roots eq 0 then return 0; end if;
    // select the first root
    root := roots[1];
    // construct the polynomial in R[z] representing the isomorphisme between X and Y
    s := R!Eltseq(Y!root);
    return s;
end function;
function InverseFieldIsomorphism(f,g,s)
    p := Characteristic(BaseRing(Parent(f)));
    Fp := GF(p);
    X<x> := ext<Fp | f>;
    Y<y> := ext<Fp | g>;
    R<z> := PolynomialRing(Fp);
    // this time we will find the roots of g in the field X, to
    roots := root_calculation(X,g);
    if #roots eq 0 then return 0; end if;
    for root in roots do   
        // n distinct roots and one of them will be desired phi(x)
        if X ! Evaluate(s,R ! Eltseq(X !root)) eq x then return R ! Eltseq(X !root); end if;
    end for;  
end function;

//----------------------------Task 2--------------------------------//
// task 2.a
function SampleChi(n)
    // returns sequence c of integers of length n with eeach element sampled in Chi ([-1,0,1] in our case)
    // note c is type SeqEnum(RndIntElt)
    c := [];
    for i in [1..n] do
        Append(~c, Random(-1, 1));
    end for;
    return c;
end function;
//task 2.b
function FFIPKeyGen(p, n)
    Fp := GF(p); 
    R<z> := PolynomialRing(Fp); 
    // non-leading coefficient are sampled from Chi
    // hn I have irreductible pol ---> solution fouuuund
    repeat g := R!(SampleChi(n) cat [1]);
    until IsIrreducible(g);
    repeat f := R!(SampleChi(n) cat [1]);
    until IsIrreducible(f);
    // compute isomporphism
    s := FieldIsomorphism(f, g);
    //compute its inverse
    t := InverseFieldIsomorphism(f, g,s);
    // secret key is a quadruple of polynomials in ring
    return f,g,s,t;
end function;
//task 2.c
function FFIPEncrypt(m,g,s)
    n := #m; // m is a bit-string of length n
    p := Characteristic(BaseRing(Parent(g)));
    Fp := GF(p);
    Y<y> := ext<Fp | g>;
    R<z> := PolynomialRing(Fp);
    x := R.1; // generator of R because I do not have access to f
    // embed it in X as m = sum(m_ix^(i-1) , i=1...n )
    // but do not forget to convert my bits from string to integer
    mX := &+[StringToInteger(m[i])*x^(i-1): i in [1..n]];
    // construct the noise term as sumR[i]*x^(i-1)
    chi := SampleChi(n);
    r_e := &+[chi[i]*x^(i-1): i in [1..n]];
    // compute noisy message as m+2r
    m_prime := mX + 2*r_e;
    // compute the elemnt c = phi(m') (in Y)  
    c := Evaluate(R ! Eltseq(m_prime),s);
    //then the ciphertext c is a polynomial in R of degree less than n
    ciphertext := R ! Eltseq(Y ! c);
    return ciphertext;
end function;
//task 2d
function FFIPDecrypt(c,f,t)
    p := Characteristic(BaseRing(Parent(f)));
    Fp := GF(p);
    R<z> := PolynomialRing(Fp); 
    X<x> := ext<Fp | f>;
    // compute the image m'(in X) under inverseIso(c)
    m_prime := X ! Evaluate(c,t);
    m_2prime := "";
    k := Eltseq(m_prime);
    for i in k do
        // reduce the coefficients of m' in the symmetric onterval to obtain m''
        sym_int := ((Integers() ! i) + (p div 2)) mod p - (p div 2);
        // recover m from m'' mod 2
        // but do not forget to  convert my integers to string
        m_2prime := m_2prime cat IntegerToString(Integers() ! (Integers(2) ! sym_int));
    end for;
    return m_2prime;
end function;

//--------------------------Task 3-------------------------//
function KnownPlaintextNoiseAttack(g, cs, ms, rs)
// problem in this function because I am not able to recover f
// 
    p := Characteristic(BaseRing(Parent(g)));
    Fp := GF(p);
    R<z> := PolynomialRing(Fp);
    Y<y> := quo<R | g>;
    n := #cs;
    B := RSpace(R,n)!cs;
    A := MatrixRing(R,n)!0;
    //construct n polynoms of n different degrees
    set_pol := [];
    for i in [1..n] do
        set_pol[i] := z^(i-1);
    end for;
    for i in [1..n] do
        m_poly_Y := Y!ms[i];
        r_poly_Y := Y!(2*rs[i]);
        for j in [1..n] do 
            // m := Evaluate(ms[i], x) + 2*Evaluate(rs[i], x);
            A[i, j] := Eltseq(Evaluate(set_pol[j], m_poly_Y+r_poly_Y));
            //here problem because ms and rs are in X 
        end for;
        
    end for;
    //A; size m by n
    //B; size m by 1
    // transpose (as in the DHP+18) to have compatible matrices A and B in order to find a solution
    A_t := Transpose(A);
    if IsConsistent(A_t, B) then
        s_coeffs := Solution(A_t, B);
        s := R!Eltseq(s_coeffs);
        return s; 
    else return R!0; end if;
end function;
// no task 3d 
