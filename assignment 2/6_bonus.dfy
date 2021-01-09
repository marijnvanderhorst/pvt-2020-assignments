method ninetyone(a: int) returns (n: int)
requires 0<=a<=100;
ensures n==91;
{
    var c: int;
    c := 1;
    n := a;
    while (c != 0)
    invariant 0 <= n <= 111;
    invariant 0 <= c <= 10;
        decreases c;
        { 
            if (n > 100) 
            { 
                n := n − 10;
                c := c−1;
            } else { 
            n := n + 11;
            c := c+1;
            }
        }
    }