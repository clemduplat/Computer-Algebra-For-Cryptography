clear;
//------------------------------------task 1----------------------------------//
HpMult := function(p, u1, u2)  
    a1 := u1[1];
    b1 := u1[2];
    c1 := u1[3];
    d1 := u1[4];
    a2 := u2[1];
    b2 := u2[2];
    c2 := u2[3];
    d2 := u2[4];
    // (a_1 + b_1*i + c_1*j +d_1*k)*(a_2 + b_2*i + c_2*j + d_2*k)
    // knowing that with my specific p -> j^2 = -p and k^2 = -p  and that i^2= -1, ij= -ji
    // Calculate the product terms
    a := a1*a2 - b1*b2 - p*c1*c2 - p*d1*d2;
    b := a1*b2 + b1*a2 + p*c1*d2 - p*d1*c2;
    c := a1*c2 - b1*d2 + c1*a2 + d1*b2;
    d := a1*d2 + d1*a2 + b1*c2 - c1*b2;
    // output sequence v representing the product
    return [a, b ,c,d ];
end function;
HpNorm := function(p, u)
    a:= u[1];
    b := u[2];
    c := u[3];
    d := u[4];
    return a^2 + b^2 + p*c^2 + p*d^2;
end function;
HpAdd := function(u1, u2)
    return [u1[i] + u2[i] : i in [1..4]];
end function;

HpInv := function(p, u)
    a := u[1];
    b := u[2];
    c := u[3];
    d := u[4];
    // norm for my special case for p
    norm := HpNorm(p,u);
    // Compute the inverse using the conjugate divided by the norm
    return [a/norm, -b/norm, -c/norm, -d/norm];
end function;
//-----------------------------------------task 2----------------------------------------//
function LatticeSum(B1, B2)
    // B=[B1;B2]
    B := VerticalJoin(B1, B2);
    // print "B";
    // B;
    //HermitForm only works with integers, but we are with Rational basis -> convert them to integers using LCM of denominator
    L := LCM([Denominator(x) : x in Eltseq(B)]);
    B_int := Matrix(Integers(), NumberOfRows(B), NumberOfColumns(B), [Numerator(x)*L div Denominator(x) : x in Eltseq(B)]);
    //HermitNorm of integer matrix
    H_int := HermiteForm(B_int);
    
    // reconvert to a rational basis because it was noit correct for Joint matrix if we do not reconverted
    H := Matrix(Rationals(), NumberOfRows(H_int), NumberOfColumns(H_int), [x / L : x in Eltseq(H_int)]);
    // now I have a simplified canonical basis so I can remove the zero rows
    // print "H";
    // H;
    NonZeroRows := [r : r in Rows(H) | not IsZero(r)];
    Cleaned_H := Matrix(Rationals(), #NonZeroRows, NumberOfColumns(H), NonZeroRows);
    //return H;
    return Cleaned_H;
end function;
function LatticeIntersect(B1, B2)
    // basis of a dual lattice L^* can be derived from the basis of L : B^* = (B^T)^(-1)
    B1_dual := Transpose(B1^(-1));
    B2_dual := Transpose(B2^(-1));
    // // equality = (intersection of two lattices)^*= sum of two dual lattices -> sum of the dual lattices provides a bais for the dual of their intersection
    // Sum the dual lattices using fct 2a
    Sum_B_dual := LatticeSum(B1_dual, B2_dual);
    // Sum_B_dual; // I have an excess of zero rows -> need tp remove them
    //only interested in the rows that are not zero (because checked with Sum_B_dual_plus) 
    NonZeroRows := [r : r in Rows(Sum_B_dual) | not IsZero(r)];

    // Recreate the matrix without zero rows
    Cleaned_Sum_B_dual := Matrix(NonZeroRows);
    //LaticeSum is not working i need to reconvert it to rationals
    //Sum_B_dual_plus := BasisMatrix(Lattice(B1_dual) + Lattice(B2_dual));
    //Sum_B_dual_plus;
    return Transpose(Cleaned_Sum_B_dual^-1);
end function;

//-----------------------------task 3------------------------------//
Conjugate := function(u)
        // u_bar = a-b*i-c*j-d*k
        return [u[1], -u[2], -u[3], -u[4]];
end function;
IsMaximalOrder := function(p, B)
    n := NumberOfRows(B);
    T := Matrix(RationalField(), n, n, [0 : i in [1..n*n]]);
    for i in [1..n] do
        for j in [1..n] do
            u := HpMult(p, B[i], Conjugate(B[j])); // need to multiply u*u_bar where u= a+b*i+c*j+d*k and u_bar = a=a-b*i-c*j-d*k
            // trace is simply 2 times the real part(a)
            // T[i,j] := 2*u[1];  
            T[i,j] := 2*u[1];
        end for;
    end for;
    //T;
    detT := Determinant(T);
    //detT;
    //p^2;
    return detT eq p^2;
end function;

//---------------------------task 4-------------------------//
IdealGensToLatticeGens := function(p, O, vs)
    n := NumberOfRows(O);
    rows := [];
    // input p, 4 by 4 matrix whose rows form a basis of a maximal order 0 and a sequence containing v_1,...v_s in Q^4 representing non-zero elements of O
    //output a matrix B in Q_4by4 whose rows are a basis of I = v1*O + ... vs*O as a lattice
    for v in vs do
        // product for the current generator v with each row of O
        for i in [1..n] do
            I := HpMult(p, v, Eltseq(O[i]));
            // add for the sum -> could use LatticeSum to avoid scaling but too late
            Append(~rows, I);
        end for;
    end for;

    B := Matrix(Rationals(), #rows, 4, &cat(rows));
    
    // scale -> same steps as task 2
    L := LCM([Denominator(x) : x in Eltseq(B)]);
    B_int := Matrix(Integers(), NumberOfRows(B), NumberOfColumns(B), [Numerator(x) * L div Denominator(x) : x in Eltseq(B)]);
    
    H_int := HermiteForm(B_int);

    H := Matrix(Rationals(), NumberOfRows(H_int), NumberOfColumns(H_int), [x / L : x in Eltseq(H_int)]);
    
    NonZeroRows := [r : r in Rows(H) | not IsZero(r)];
    Cleaned_H := Matrix(Rationals(), #NonZeroRows, NumberOfColumns(H), NonZeroRows);
    
    return Cleaned_H;
end function;

function LeftMaximalOrder(p, O, vs)
    //return OL, a matrix whose rows are a basis of the maximal order O_L(I)
    //here see def of left maximal order
    //really straighforward :expresionn OL as an interwection of lattices
    I := IdealGensToLatticeGens(p, O, vs); 
    L := LatticeIntersect(O, I);
    return L;  
end function;
//----------------------task 6------------------//
ProjLattice := function(O)
    n := NumberOfRows(O);
    Oproj := ZeroMatrix(Rationals(), n, 3);

    for i in [1..n] do
        a := O[i][1];
        b := O[i][2];
        c := O[i][3];
        d := O[i][4];
        // t(u) - 2u = 2a - 2*(a + b*i + c*j +d*k)
        // therefore component "a" goes away
        Oproj[i][1] := -2 * b;  // i
        Oproj[i][2] := -2 * c;  // j
        Oproj[i][3] := -2 * d;  // k
    end for;

    // scale to integer matrix to use hermiform -> same steps as for task 2 (here want to keep only the 3 first rows)
    L := Lcm([Denominator(x) : x in Eltseq(Oproj)]);
    Oproj_int := Matrix(Integers(), NumberOfRows(Oproj), NumberOfColumns(Oproj), [Numerator(x)*L div Denominator(x) : x in Eltseq(Oproj)]);
    H_int := HermiteForm(Oproj_int);
    H := Matrix(Rationals(), NumberOfRows(H_int), NumberOfColumns(H_int), [ x / L : x in Eltseq(H_int) ]);
    NonZeroRows := [r : r in Rows(H) | not IsZero(r)];
    Cleaned_H := Matrix(Rationals(), #NonZeroRows, NumberOfColumns(H), NonZeroRows);
    //first 3 rows to have a 3 by 3 matrix
    return Cleaned_H;
end function;



OrderSignature := function(p, O)
    Oproj := ProjLattice(O);  // Project the lattice to ignore the real component

    //scaling
    scale := 10^8;  //making it bigger doesn't change
   
    Oproj_scaled:= Matrix(Rationals(), 3, 3, [
        [Round(Oproj[i,1]*scale), Round(Oproj[i,2]*(scale*Sqrt(p))), Round(Oproj[i,3]*(scale*Sqrt(p)))] : i in [1..3]
    ]);
    L := Lattice(Oproj_scaled);
    vecs := ShortestVectors(L);  // This returns a sequence of shortest vectors
    // vecs;
    vec := vecs[1];  // Take the first vector, assuming vec is not empty
    // print "vec";
    vec;

    //HP norm of a non-zero element of Oproj
    // u := [Round(0), Round(vec[1]/scale), Round(vec[2]/(scale*Sqrt(p))), Round(vec[3]/(scale*Sqrt(p)))];
    u := [0, vec[1]/scale, vec[2]/(scale*Sqrt(p)), vec[3]/(scale*Sqrt(p))];
    //u;
    // Compute signature based on the norm of the shortest vector

    sig := HpNorm(p,u);
    return Round(sig);
end function;


//------------------------Task 7-----------------------------//
function GetMaximalOrder(p)
    Lattice4 := Matrix(Rationals(), 4, 4, [1,0,0,0, 0,1,0,0, 0,1/2,1/2,0, 1/2,0,0, 1/2]);
    return Lattice4; 
end function;
function KeyGen(p, l)
    //Your code is indeed too naive to work for large values of p (the probability of success is way too small, which is why your code runs endlessly).
    //In particular, your use of IsSquare is not as intended by the hint in Task 7.
    //The goal is to proceed as discussed in the paragraph preceding the task description: take b, c, d random, and then use Magma to find a such that
    //a^2 = -b^2 - p*c^2 - p*d^2 modulo ell^e.
    //For this you can work in the ring of integers modulo ell^e, which in Magma you can invoke via Integers(ell^e). IsSquare will not only tell you whether or not the right hand side is a square, but in case it is, it will also return a square root.
    e := Ceiling(Log(l, p));  // e= [log_l(p)] _> scaling factor
    // initial code -> endless run for big p
    // we will now working with this to simplify computations by doing modulo
    // -> transform any infinte field into a finite field of integers
    Z_ell_e := Integers(l^e);  // ring of integers modulo ell^e
    //computing the basis of the maximal order iv)
    O := GetMaximalOrder(p);
    repeat
        //take b, c, d random
        b := Random(l^e);
        c := Random(l^e);
        d := Random(l^e);
        //a^2 = -b^2 - p*c^2 - p*d^2 modulo ell^e.
        a_square := -(b^2 + p*c^2 + p*d^2) mod l^e;
        //IsSquare will not only tell you whether or not the right hand side is a square, but in case it is, it will also return a square root.
        //right hand side is_square
        // square root of a^2
        is_square, a := IsSquare(Z_ell_e!a_square); // Z/l^eZ
        // if the norm condition can or cannot be satisfied
        if is_square then
            a := IntegerRing()!a;
            u := [a, b, c, d];
            ///norm smust be divisible by l^e
            if HpNorm(p, u) mod l^e eq 0 then
                // compute the ideal I = l^e * O + u * O
                v := [l^e, 0, 0, 0];
                vs := [v, u];
                // left order
                OL_I := LeftMaximalOrder(p, O, vs);
                return u, OL_I;
    
            end if;
        end if;
    until false;
    

    
end function;
//---------------Task 9---------------------------------------//
ExtractKey := function(p, l, pk, sk)
    // compute the relative norms
    e := Ceiling(Log(l, p));
    m := (l eq 2) select 3 else 2; //m (2 or 3) but different from l
    ebis := Ceiling(Log(m, p));
    v := [m^ebis, 0, 0, 0];
    u := [l^e * sk[i] : i in [1..4]];
    // combined vector
    vs := [v, u];
    // left maximal order
    OL_I_J := LeftMaximalOrder(p, Matrix(Rationals(), pk), vs);
    // finally I have my signature
    key := OrderSignature(p, OL_I_J);
    return key;
end function;
