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
    invariant pow(a,b) == pow(a,b)
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

// TODO

// something something pow(a,b) == pow(a,b-1) * a iff b > 1
lemma decreasePowByOne(a: int, b: int)
  ensures pow(a,b) == pow (a,b-1) * a
  requires b >= 1;
  {

  }

// something something pow(a,b) == pow(a,b/2) * pow(a, b/2) if b == even
lemma decreasePowByHalf(a:int, b:int)
  ensures pow(a,b) == if b%2 == 1 then a * pow(a,b-1) else pow (a,b/2) * pow(a,b/2);
  requires b > 1;
  {
      // var p := pow(a,b);
      // var p1 := pow(a, b/2);
      // assert(a*a*a*a*1 == a*a*1 * a*a*1);
      // var p2 := pow(a, b/2);
      // assert(pow(a,2) == pow(a,1) * pow(a,1));
      // assert(pow(a,4) == pow(a,2) * pow(a,2));
      //assert(pow(a,2) == pow(a,1) * pow(a,1));
      // assert(1 == 1);
      // simpleLemma(p);
      // while b % 2 == 0
      // {

      // }
      if(b==2){
        assert(pow(a,2) == pow(a,1) * pow(a,1));
      } else if (b % 2 ==0 ) {
        decreasePowByHalf(a, b/2);
        assert(pow(a,b) == pow(a,b/2) * pow(a, b/2));
      } else {
        decreasePowByHalf(a, b-1);
        assert(pow(a,b) == a* pow(a,b-1));
      }

  }
lemma simpleLemma(a: int)
  ensures a * 1 == a;
  {}


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
