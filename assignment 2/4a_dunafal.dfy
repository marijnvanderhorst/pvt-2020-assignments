/* Dutch National Flag
 * sort an array that has three different keys
 */

datatype Color = Red | White | Blue

// ordering of colors: Red > White > Blue
predicate Above(c: Color, d: Color)
{
  c == Red || (c == White && d != Red) || (c == Blue && d != Red && d != White)
}

method {:verify true}sortFlag(a: array<Color>)
  modifies a // needed for arrays (since they are objects, not values such as sequences)
  ensures forall i,j | 0 <= i < j < a.Length :: Above(a[i], a[j])
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  var N := a.Length;
  var r, w, u := 0, 0, N; // marks the red part, white part, unsorted part
  while u > w
    /*
      0                    r                  w             wu         N
      RRRRRRRRRRRRRRRRRRRRRWWWWWWWWWWWWWWWWWWWXXXXXXXXXXXXXXXBBBBBBBBBB

    */
    invariant 0 <= r <= w <= u <= N
    invariant multiset(a[..]) == multiset(old(a[..]))
    invariant forall k :: 0 <= k < r ==> a[k] == Red;
    invariant forall k :: r <= k < w ==> a[k] == White;
    invariant forall k :: u <= k < N ==> a[k] == Blue;
    decreases u - w;
  {
    if(a[w] == Blue){
      u := u-1;
      swap(a, w, u);
    } else
    if (a[w] == Red){
      swap(a, r, w);
      w := w + 1;
      r := r + 1;
    } 
    else { //(a[w] == White)
     w := w + 1;
    }

    //a[r], a[w] := a[w], a[r];
  }
}

method {:verify true} swap(a: array<Color>, i: nat, j: nat)
  modifies a;
  requires 0 <= i <= j < a.Length;
  ensures a[i] == old(a[j]) && a[j] == old(a[i])
  ensures forall k | 0 <= k < a.Length && k!= i && k!= j :: a[k] ==old(a[k])
  ensures multiset(a[..]) == multiset(old(a[..]))
  //everything outside i and j remains unchanged
{

      a[i], a[j] := a[j], a[i];
}

method testColordering() {
  assert Above(Red, White);
  assert Above(White, Blue);
  assert Above(White, White);
}
