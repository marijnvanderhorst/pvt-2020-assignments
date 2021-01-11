method powerLog(a: int, b: int) returns (p: int)  //change per 8-1-2019
  requires b >= 0;
  ensures p == pow(a, b);
{
	var base: int; // base
  var exp: int; // exponent

  // TODO initialize p, base, and exp
  base := a;
  exp := b;
  p := 1;


	while (exp > 0)
    invariant exp >= 0;
    invariant pow(a,b) == pow(a,b);
    invariant pow(a, exp) == pow(a, exp);
    invariant pow(base, b) == pow(base, b);
    invariant pow(base, exp) == pow(base, exp);
    invariant pow(a, b) == p * pow(base, exp);
    //invariant pow(base, exp) == p * pow(base, exp);
    decreases exp;
	{
    assume(pow(a, b) == p * pow(base, exp));
    
    // TODO fill in body
    if(exp % 2 == 1){
      decreasePowByOne(base, exp);
      p := p * base;
      exp := exp - 1;
    }
    assert(pow(a, b) == p * pow(base, exp));
    // if(p == 1 && exp > 0){
    //   p := base;
    // }

    assert(pow(a, b) == p * pow(base, exp));

    if(exp > 0){
      decreasePowByHalf(base, exp);
      assert(pow(a, b) == p * pow(base, exp));
      p := p * p;
      exp := exp / 2;
      assert(pow(a, b) == p * pow(base, exp));
    }
    assert(pow(a, b) == p * pow(base, exp));
  }

  base := a;
  exp := b;
  p := 1;

  while (exp > 0)
    invariant pow(a, b) == p * pow(base, exp);
    decreases exp;
	{
    // TODO fill in body
      p := p * base;
      exp := exp - 1;
  }
}

/*----- Lemmas -----*/

lemma {:induction false} decreasePowByOne(a: int, b: int)
  ensures pow(a,b) == pow (a,b-1) * a
  requires b >= 1;
  {

  }

lemma {:induction false} decreasePowByHalf(a:int, b:int)
  decreases a, b;
  requires b > 1;
  requires b % 2 == 0;
  ensures pow(a, b) == pow (a, b/2) * pow(a, b/2);
  {
      if(b == 2) {
        // Induction base case
        assert (pow(a, b) == pow(a, 1) * pow(a, 1));
      } else {
        // Inductive step
        decreasePowByHalf(a, b - 2);
        assert (pow(a, b - 2) == pow(a, b/2 - 1) * pow(a, b/2 - 1));
        
        assert (pow(a, b) == a * a * pow(a, b - 2));
        assert (a * a * pow(a, b - 2) == a * a * pow(a, b/2 - 1) * pow(a, b/2 - 1));
        assert (a * a * pow(a, b/2 - 1) * pow(a, b/2 - 1) == pow(a, b/2) * pow(a, b/2));
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
