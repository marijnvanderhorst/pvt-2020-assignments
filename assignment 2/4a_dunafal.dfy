/**
 * 2IMP10, Program verification techniques, Assignment 2, Excercise 4a.
 *
 * M. van der Horst (1000979 - m.v.d.horst@student.tue.nl)
 * T.M. Verberk (1016472 - t.m.verberk@student.tue.nl)
 */

/* Dutch National Flag
 * sort an array that has three different keys
 */

datatype Color = Red | White | Blue

// ordering of colors: Red > White > Blue
// Ensures that the array is properly divided.
// Returns FALSE if color of d comes before the color of c
predicate Above(c: Color, d: Color)
{
  c == Red || (c == White && d != Red) || (c == Blue && d != Red && d != White)
}

/*
 * Sorts a flag on 3 colors
 */
method {:verify true}sortFlag(a: array<Color>)
  modifies a // needed for arrays (since they are objects, not values such as sequences)
  ensures forall i,j | 0 <= i < j < a.Length :: Above(a[i], a[j]) // Ensures the array is correctly sorted
  ensures multiset(a[..]) == multiset(old(a[..])) //Ensures no elements are added or removed
{
  var N := a.Length;
  var r, w, u := 0, 0, N; // marks the red part, white part, unsorted part
  while u > w
    /*
      0                    r                  w             wu         N
      RRRRRRRRRRRRRRRRRRRRRWWWWWWWWWWWWWWWWWWWXXXXXXXXXXXXXXXBBBBBBBBBB

    */
    invariant 0 <= r <= w <= u <= N // Ensures that the indices are within array ranges
    invariant multiset(a[..]) == multiset(old(a[..])) //makes sure that no items are added or removed
    invariant forall k :: 0 <= k < r ==> a[k] == Red; // Ensures that all elements before index r are RED
    invariant forall k :: r <= k < w ==> a[k] == White; // Ensures that alle elements from index r untill and excluding index w are WHITE
    invariant forall k :: u <= k < N ==> a[k] == Blue; // Ensures that all elements after index u are BLUE
    decreases u - w; // Decreases u-w
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

//Swap method to swap two elements in an array
method {:verify true} swap(a: array<Color>, i: nat, j: nat)
  modifies a; // the swap modifies the array
  requires 0 <= i <= j < a.Length; // The indices of the to swap elements should be within the range of the array
  ensures a[i] == old(a[j]) && a[j] == old(a[i]) // At the end the element at position j is at position i and vice versa.
  ensures forall k | 0 <= k < a.Length && k!= i && k!= j :: a[k] ==old(a[k]) // Ensures that no other elements besides a[i] and a[j] are changed
  ensures multiset(a[..]) == multiset(old(a[..])) // Ensures that there the multiset is the same.
{

      a[i], a[j] := a[j], a[i];
}

//Method that tests the ordering to make sure there are no unnecessary errors
method testColordering() {
  assert Above(Red, White);
  assert Above(White, Blue);
  assert Above(White, White);
}
