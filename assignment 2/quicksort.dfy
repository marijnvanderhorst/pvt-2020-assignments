/* Quicksort
 * sort an array ascendingly
 */

method Partition(a: array<int>, lo: int, hi: int) returns (pivot: int)
  modifies a;
  requires 0 <= lo < hi < a.Length;
  requires 0 < lo ==> Partitioned(a, 0, lo - 1, lo, hi);
  requires hi < a.Length - 1 ==> Partitioned(a, lo, hi, hi + 1, a.Length - 1);

  ensures lo <= pivot <= hi;
  ensures forall k | 0 <= k < lo || hi < k < a.Length :: a[k] == old(a[k]);
  ensures multiset(a[..]) == multiset(old(a[..]));
  ensures a[pivot] == old(a[hi]);
  ensures forall k | lo <= k <= hi && k < pivot :: a[k] < old(a[hi]);
  ensures forall k | lo <= k <= hi && k >= pivot :: a[k] >= old(a[hi]);

  ensures 0 < lo ==> Partitioned(a, 0, lo - 1, lo, hi);
  ensures hi < a.Length - 1 ==> Partitioned(a, lo, hi, hi + 1, a.Length - 1);
  ensures lo < pivot ==> Partitioned(a, 0, pivot - 1, pivot, pivot);
  ensures pivot < hi ==> Partitioned(a, 0, pivot, pivot + 1, hi);
{
  var pVal := a[hi];
  pivot := lo; // Will eventually contain the index of the pivot after partitioning.
  var j := lo;

  while (j < hi) 
    decreases hi - j;
    invariant lo <= pivot <= j <= hi; // pivot index and j remain inside bounds
    invariant forall k | 0 <= k < lo || hi < k < a.Length :: a[k] == old(a[k]);
    invariant a[hi] == pVal; // pivot value remains at the end of the array
    invariant forall k | lo <= k < pivot :: a[k] < pVal; // values before pivot are smaller
    invariant forall k | pivot <= k < j :: pVal <= a[k]; // values after pivot greater or equal
    invariant multiset(a[..]) == multiset(old(a[..])) // array always contains the same values
    invariant 0 < lo ==> Partitioned(a, 0, lo - 1, lo, hi);
    invariant hi < a.Length - 1 ==> Partitioned(a, lo, hi, hi + 1, a.Length - 1);
  {
    if (a[j] < pVal) {
      swap(a, pivot, j);
      pivot := pivot + 1;
    }

    j := j + 1;
  }

  swap(a, pivot, hi);
}

method {:verify true}Quicksort(a: array<int>, lo: int, hi: int)
  modifies a // needed for arrays (since they are objects, not values such as sequences)
  requires 0 <= lo <= hi < a.Length;
  requires 0 < lo ==> Partitioned(a, 0, lo - 1, lo, hi);
  requires hi < a.Length - 1 ==> Partitioned(a, lo, hi, hi + 1, a.Length - 1);
  ensures forall k | 0 <= k < lo || hi < k < a.Length :: a[k] == old(a[k]);
  ensures Sorted(old(a), 0, lo) ==> Sorted(a, 0, lo);
  ensures Sorted(old(a), hi, a.Length - 1) ==> Sorted(a, hi, a.Length - 1);
  ensures Sorted(a, lo, hi);
  ensures multiset(a[..]) == multiset(old(a[..]));
  ensures 0 < lo ==> Partitioned(a, 0, lo - 1, lo, hi);
  ensures hi < a.Length - 1 ==> Partitioned(a, lo, hi, hi + 1, a.Length - 1);
  decreases hi-lo;
{
  if (lo == hi) {
    return;
  }

  var pivot := Partition(a, lo, hi);
  var loVal := a[lo];

  if (pivot > lo) {
    Quicksort(a, lo, pivot - 1);
  } 

  if (pivot < hi) {
    Quicksort(a, pivot + 1, hi);
  } 
}

/*----- Lemmas -----*/
lemma {:induction false} test(a: array<int>, lo: int, hi: int, n: int)
  requires 0 <= lo <= hi < a.Length;
  requires Sorted(a, lo, hi);
  requires n <= a[lo];
  ensures forall k | lo <= k <= hi < a.Length :: n <= a[k];
  decreases hi - lo;
  {
    if (lo == hi) {

    } else {
      test(a, lo + 1, hi, n);
    }
  }

lemma {:induction false} lemmaSortedTransitive(a: array<int>, lo: int, hi: int)
  // reads a;
  requires 0 <= lo <= hi < a.Length;
  requires Sorted(a, lo, hi);
  ensures forall i,j | lo <= i <= j <= hi < a.Length :: a[i] <= a[j];
  decreases hi - lo;
  {
    if (lo == hi) {

    } else {
      lemmaSortedTransitive(a, lo + 1, hi);
      assert (a[lo] <= a[lo + 1]);
    }
  }

predicate Partitioned(a: array<int>, lo1: int, hi1: int, lo2: int, hi2: int)
  reads a;
  requires 0 <= lo1 <= hi1 <= lo2 <= hi2 < a.Length;
  {
    forall i,j | lo1 <= i <= hi1 < lo2 <= j <= hi2 :: a[i] <= a[j]
  }

predicate Sorted(a:array<int>, lo: int, hi:int)
  reads a;
  requires 0 <= lo <= hi < a.Length;
  {
    forall i | lo <= i < hi :: a[i] <= a[i+1]
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
