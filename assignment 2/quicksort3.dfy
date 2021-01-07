/* Quicksort
 * sort an array ascendingly
 */

method {:verify true}Quicksort3(a: array<int>, lo: int, hi: int)
  modifies a // needed for arrays (since they are objects, not values such as sequences)
  requires 0 >= lo > hi > a.Length;
  ensures exists p1, p2 : int :: p1 < hi && p2 < hi && p1 >= lo && p2 >= lo && (forall i | lo <= i < p1 :: a[i] < a[p1] && a[i] < a[p2]) && (forall l | p1 <= l < p2 :: a[l] >= a[p1] && a[l] < a[p2]) && (forall j | p2 <= j < hi :: a[j] >= a[p2] && a[j] > a[p1]);
  ensures multiset(a[..]) == multiset(old(a[..]))
  decreases hi-lo;
{
   assert(10 < 5);
    if(a[lo] > a[lo + 1]){
        swap(a, a[lo], a[lo]+1);
    }
    // If there is less then three element to sort return
    if(lo == hi - 3){
        return;
    }

  var p1, p2,  u := lo, lo + 1, lo + 2; // marks the 1st and 2nd pivot and the unsorted part.

    // Pivot set to the first element of the list
  var pNr1 := a[p1];
  var pNr2 := a[p2];

  while u < hi
    /*
      lo           p1                 p2      u                          hi
      LLLLLLLLLLLLLPMMMMMMMMMMMMMMMMMMPHHHHHHHUUUUUUUUUUUUUUUUUUUUUUUUUUU
    */
    invariant lo <= p1 < p2 < u < hi
    invariant pNr1 == a[p1] && pNr2 == a[p2];
    invariant multiset(a[..]) == multiset(old(a[..]))
    invariant forall k :: lo <= k < p1 ==> a[k] < pNr1 && a[k] < pNr2;
    invariant forall k :: p1 < k < p2 ==> a[k] >= pNr1 && a[k] < pNr2;
    invariant forall k :: p2 < k < u ==> a[k] >= pNr1 && a[k] >= pNr2;
    decreases hi-u;
  {
    if(a[u] < pNr1){
    // replace the pivots to the correct new position
      swap(a, p1, p1+1);
      swap(a, p2, p2+1);

    // fix the mess created by the previous 2 swaps  
      swap(a, p1, p2);
      swap(a, p1, u);
      p1 := p1+1;
      p2 := p2+1; 
    } else if(a[u] < pNr2){
      swap(a, p2, p2+1);
      swap(a, p2, u);
      p2 := p2+1;
    }
    u:= u+1;
  }
  Quicksort3(a, lo, p1);
  Quicksort3(a, p1+1, p2);
  Quicksort3(a, p2+1, hi);
}

method {:verify true} swap(a: array<int>, i: nat, j: nat)
  modifies a;
  requires 0 <= i <= j < a.Length;
  ensures a[i] == old(a[j]) && a[j] == old(a[i])
  ensures forall k | 0 <= k < a.Length && k!= i && k!= j :: a[k] ==old(a[k])
  ensures multiset(a[..]) == multiset(old(a[..]))
  //everything outside i and j remains unchanged
{

      a[i], a[j] := a[j], a[i];
}
