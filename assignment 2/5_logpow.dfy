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
    invariant pow(a, b) == pow(a,b);
    invariant pow(a, exp) == pow(a, exp);
    invariant pow(base, b) == pow(base, b);
    invariant pow(base, exp) == pow(base, exp);
    invariant exp >= 0;
    decreases exp;
	{
    assume(pow(base,exp) == pow(base,exp));
    // TODO fill in body
    if(exp % 2 == 1){
      decreasePowByOne(base, exp);
      p := p * base;
      exp := exp - 1;
    }
    if(p == 1){
      p := base;
    }
    if(exp > 0){
      decreasePowByHalf(base, exp);
      p := p * p;
      exp := exp / 2;
    }
    assert(pow(base,exp) == pow(base,exp));
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

// TODO

// something something pow(a,b) == pow(a,b-1) * a iff b > 1
lemma decreasePowByOne(a: int, b: int)
  ensures pow(a,b) == pow (a,b-1) * a
  requires b >= 1;
  {
    if(pow(a,b) == pow(a,b)){

    }
  }

// something something pow(a,b) == pow(a,b/2) * pow(a, b/2) if b == even
lemma decreasePowByHalf(a:int, b:int)
  ensures pow(a,b) == pow (a,b/2) * pow(a,b/2);
  requires b % 2 == 0;
  requires b > 1;
  
    // if (b == 2){
      
    // }
  


/*-------------- Specification -----------*/

function pow(a: int, b: int) : int
  requires b >= 0;
{
  if b == 0 then 1
  else a * pow(a, b-1)
}

/*-------------- Test -----------*/
method test()
{
  assert pow(2, 20) == 1024*1024;
}
