/* Mauratius national flag
 * sort an array that has three different keys
 */

// the colours of the Mauratius national flag are red, Yellow, yellow, green
datatype Color = Red | Blue | Yellow | Green 

// ordering of colors: Red > Blue > Yellow > Green
predicate Above(c: Color, d: Color)
{
  // c == Red || (c == Blue && d != Red) ....
  c == Red || 
  (c == Blue && d != Red) ||
  (c == Yellow && d != Red && d != Blue) ||
  (c == Green && d!= Red && d!= Blue && d != Yellow)
}

method {:verify true}sortFlag(a: array<Color>)
  modifies a // needed for arrays (since they are objects, not values such as sequences)
  ensures forall i,j | 0 <= i < j < a.Length :: Above(a[i], a[j])
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  var N := a.Length;
  var r, b, y, u := 0, 0, N, N; // marks the red part, Blue part, yellow part ,unsorted part
  while u > b
    /*
      0                    r                  b              u         y             N
      RRRRRRRRRRRRRRRRRRRRRBBBBBBBBBBBBBBBBBBBXXXXXXXXXXXXXXXYYYYYYYYYYGGGGGGGGGGGGGG

    */
    invariant 0 <= r <= b <= u <= y <= N
    invariant multiset(a[..]) == multiset(old(a[..]))
    invariant forall k :: 0 <= k < r ==> a[k] == Red;
    invariant forall k :: r <= k < b ==> a[k] == Blue;
    invariant forall k :: u <= k < y ==> a[k] == Yellow;
    invariant forall k :: y <= k < N ==> a[k] == Green;
    decreases u - b;
  {
    if (a[b] == Green){
        u := u-1;
        swap(a, b, u);
        y := y-1;
        swap(a, u, y);
        
    }
    else if(a[b] == Yellow){
      u := u-1;
      swap(a, b, u);
    } else
    if (a[b] == Red){
      swap(a, r, b);
      b := b + 1;
      r := r + 1;
    } 
    else { //(a[b] == Blue)
     b := b + 1;
    }
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
  assert Above(Red, Blue);
  assert Above(Blue, Yellow);
  assert Above(Yellow, Green);
}
