/* Quicksort
 * sort an array ascendingly
 */

method {:verify true}Quicksort(a: array<int>, lo: int, hi: int)
  modifies a // needed for arrays (since they are objects, not values such as sequences)
  requires 0 <= lo <= hi <= a.Length; // lo can be equal to high if there are no elements placed in front of the pivot
  ensures Sorted(a, lo, hi);
  // Make sure that all the elements are lower than the element after this segment
  //ensures hi == a.Length || forall j :: lo <= j < hi ==> a[j] < a[hi];
  // Make sure that all the elements are higher or equal than the element before this segment
  //ensures lo == 0 || forall j :: lo <= j < hi ==> a[j] >= a[lo]
  ensures forall k | 0 <= k < lo :: a[k] ==old(a[k]);
  ensures forall k | hi <= k < a.Length :: a[k] == old(a[k]);
  //ensures lo == a.Length || BetweenLower(a, 0, lo);
  //ensures BetweenHigher(a, hi, a.Length-1);
  ensures hi == a.Length || a[hi] == old(a[hi]);
  //(exists p : int :: p < hi && p >= lo && forall i | lo <= i < p :: a[i] < a[p] && forall j | p <= i < hi :: a[j] > a[p]);
  // make sure parts not affected are the same
  ensures multiset(a[..]) == multiset(old(a[..]))
  decreases hi-lo;
{
    //assert(10<5);

    // EG lo == 5
    // EG hi == 6,7 do nothing
    //assert(lo == a.Length || BetweenLower(a, 0, lo));

    // If there is less then two element to sort return
    if(lo > hi - 2){
        return;
    }
  
  var p, u := lo, lo + 1; // marks the pivot and the unsorted part.

    // Pivot set to the first element of the list
  var pNr := a[p];


  assert(forall k | 0 <= k < lo :: a[k] ==old(a[k]));

  while u < hi
    /*
      lo           p                      u                          hi
      LLLLLLLLLLLLLPHHHHHHHHHHHHHHHHHHHHHHUUUUUUUUUUUUUUUUUUUUUUUUUUU

    */
    invariant lo <= p < u <= hi
    invariant pNr == a[p];
    invariant multiset(a[..]) == multiset(old(a[..]))
    invariant forall k :: lo <= k < p ==> a[k] < pNr;
    invariant forall k :: p < k < u ==> a[k] >= pNr;
    invariant forall k | 0 <= k < lo :: a[k] ==old(a[k]);
    invariant forall k | hi <= k < a.Length :: a[k] == old(a[k]);
    decreases hi-u;
  {
    if(a[u] < pNr){
      // swap two element such that the element lower than p is now at position p+1;
      swap(a, p+1, u);
      // swap the pivot and the element after it.      
      swap(a, p, p+1);
      // increase p;
      p:= p+1; 
    }
    u:= u+1;
  }
  assert(forall k | 0 <= k < lo :: a[k] ==old(a[k]));

  assert(forall j :: p < j < hi ==> a[j] >= a[p]);
  assert(forall j :: lo <= j < p ==> a[j] < a[p]);
  assert(BetweenLower(a, lo, p));
  assert(BetweenHigher(a, p, hi-1));

  Quicksort(a, lo, p);
  assert(forall j :: p < j < hi ==> a[j] >= a[p]);
  
  assert(Sorted(a, lo, p));

  assert(Sorted(a, lo ,p+1));
  assert(BetweenLower(a, lo, p));
  
  assert(forall j :: p < j < hi ==> a[j] >= a[p]);
  //assert(forall j :: lo <= j < p ==> a[j] < a[p]);
  Quicksort(a, p+1, hi);
  //assert(forall j :: lo <= j < p ==> a[j] < a[p]);


  assert(Sorted(a, p+1, hi));
  assert(Sorted(a, p, hi));
  
  assert(Sorted(a, lo, hi));
  assert(forall k | hi <= k < a.Length :: a[k] == old(a[k]));

}

//predicate Sorted?(a:seq<int>, lo: int, hi:int){
  //forall i,j a[i] <= a[j]
  //forall k .... a[k] < a[k+1];
//}

predicate Sorted(a:array<int>, lo: int, hi:int)
  reads a;
  requires 0 <= lo <= hi <= a.Length;
  //ensures (lo == a.Length || forall k | 0 <= k < lo :: a[k] < a[lo]);
  ensures forall j | hi > j > a.Length :: a[j] < a[hi];
  
  {
    forall i :: lo < i < hi-1 ==> a[i] <= a[i+1]
    //forall i, j :: lo < i < j < hi-1  ==> a[i] <= a[j]
    //(forall i :: lo <= i < hi-1 ==> a[i] <= a[i+1]) || (forall i :: lo < i <= hi-1 ==> a[i-1] <= a[i])
  }

//All values before a certain index must be lower than this specific number
predicate BeforeLower(a:array<int>, lo: int)
  reads a;
  requires 0 <= lo < a.Length;
  {
    forall j :: 0 <= j < lo ==> a[j] < a[lo]
  }

predicate BetweenLower(a:array<int>, lo: int, hi: int)
  reads a;
  requires 0 <= lo <= hi < a.Length;
  {
    forall j :: lo <= j < hi ==> a[j] < a[hi]
  }

//All values after a certain index must be higher than this specific number
predicate AfterHigher(a:array<int>, hi: int)
  reads a;
  requires 0 <= hi < a.Length;
  {
    forall j :: hi < j < a.Length ==> a[j] >= a[hi]
  }

predicate BetweenHigher(a:array<int>, lo: int, hi: int)
  reads a;
  requires 0 <= lo <= hi < a.Length;
  {
    forall j :: lo <= j < hi ==> a[j] >= a[lo]
  }

//sorted a, k, l

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
