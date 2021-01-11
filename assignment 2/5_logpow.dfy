/**
 * 2IMP10, Program verification techniques, Assignment 2, Excercise 5.
 *
 * M. van der Horst (1000979 - m.v.d.horst@student.tue.nl)
 * T.M. Verberk (1016472 - t.m.verberk@student.tue.nl)
 */

method powerLog(a: int, b: int) returns (p: int)  //change per 8-1-2019
  requires b >= 0;
  ensures p == pow(a, b);
{
  // Edge case
  if (b == 0) {
    return 1;
  }

	var base: int; // base
  var exp: int; // exponent

  base := a; // Initialize base with a
  exp := b; // Initialize exponent with b
  p := 1; // Will eventually contain the result

  // Iterative square-and-multiply implementation
	while (exp > 1)
    invariant exp >= 1;
    invariant p * pow(base, exp) == pow(a, b);
    decreases exp;
	{
    if(exp % 2 == 0){ // exponent even
      lemmaSqBaseHalfExp(base, exp);
      
      base := base * base; // Square the base
      exp := exp / 2; // Half the exponent

    } else { // exponent odd
      p := p * base; // Multiply p by base
      exp := exp - 1; // Decrease exponent
    }
  }

  assert (exp == 1);
  assert (pow(base, exp) == base);

  p := p * base; // Compute the result
}

/*----- Lemmas -----*/
lemma {:induction false} lemmaSqBaseHalfExp(a: int, b: int)
  requires b >= 0;
  requires b % 2 == 0;
  ensures pow(a, b) == pow(a * a, b / 2);
  decreases a, b;
  {
    // Proof by induction
    if (b == 0) { // Base case
      assert (pow(a, 0) == 1);
      assert (pow(a * a, 0) == 1);
    } else if (b == 2) { // Base case
      assert (pow(a, 2) == a * pow(a, 1) == a * a);
      assert (pow(a * a, 1) == a * a);
    } else { // Inductive step
      lemmaSqBaseHalfExp(a, b - 2);
      assert (pow(a, b) == a * a * pow(a, b - 2));
      assert (pow(a, b - 2) == pow(a * a, b/2 - 1));
    }
  }

/*-------------- Specification -----------*/
function pow(a: int, b: int) : int
  requires b >= 0;
  decreases a,b;
{
  if b == 0 then 1
  else a * pow(a, b-1)
}

/*-------------- Test -----------*/
method test()
{
  assert pow(2, 20) == 1024*1024;
}
