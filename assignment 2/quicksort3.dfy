/**
 * 2IMP10, Program verification techniques, Assignment 2, Excercise 7.
 *
 * M. van der Horst (1000979 - m.v.d.horst@student.tue.nl)
 * T.M. Verberk (1016472 - t.m.verberk@student.tue.nl)
 */

/**
 * Swaps the elements at index i and j in the given array a.
 */
method {:verify true} swap(a: array<int>, i: nat, j: nat)
  modifies a; // needed for arrays (since they are objects, not values such as sequences)

  requires 0 <= i < a.Length; // i must be within bounds
  requires 0 <= j < a.Length; // j must be within bounds
  
  ensures a[i] == old(a[j]) && a[j] == old(a[i]); // elements at index i and j are swapped
  ensures forall k | 0 <= k < a.Length && k != i && k != j :: a[k] == old(a[k]); // The other elements remain untouched
{
  a[i], a[j] := a[j], a[i];
}

/**
 * Uses the last element of the given sub-array a[lo..hi] as the pivot, and partitions the array such that all elements
 * that are smaller than the pivot are before the pivot.
 */
method Partition(a: array<int>, lo: int, hi: int) returns (pivot: int)
  modifies a; // needed for arrays (since they are objects, not values such as sequences)
  
  requires 0 <= lo < hi < a.Length; // lo and hi must be within bounds
  requires 0 < lo ==> Partitioned(a, 0, lo - 1, lo, hi); // Assume that the first part is already partitioned
  requires hi < a.Length - 1 ==> Partitioned(a, lo, hi, hi + 1, a.Length - 1); // Assume last part partiioned

  ensures lo <= pivot <= hi; // Ensure pivot is within bounds
  ensures forall k | 0 <= k < lo || hi < k < a.Length :: a[k] == old(a[k]); // Ensure other part of array is untouched
  ensures a[pivot] == old(a[hi]); // Ensure that the pivot element is the last element of the input array
  ensures forall k | lo <= k < pivot :: a[k] < old(a[hi]); // Ensure partitioning within lo..hi bounds
  ensures forall k | pivot <= k <= hi :: a[k] >= old(a[hi]); // Ensure partitioning within lo..hi bounds
  ensures 0 < lo ==> Partitioned(a, 0, lo - 1, lo, hi); // Ensure first part is still partitioned
  ensures hi < a.Length - 1 ==> Partitioned(a, lo, hi, hi + 1, a.Length - 1); // Ensure last part is still partitioned
  ensures lo < pivot ==> Partitioned(a, 0, pivot - 1, pivot, hi); // Ensure partitioning within lo..hi bounds
  ensures pivot < hi ==> Partitioned(a, 0, pivot, pivot + 1, hi); // Ensure partitioning within lo..hi bounds
{
  var pVal := a[hi]; // Store the pivot value
  pivot := lo; // Will eventually contain the index of the pivot after partitioning
  var j := lo; // Index for the while-loop, starting at lower bound

  while (j < hi) 
    decreases hi - j;
    
    invariant lo <= pivot <= j <= hi; // pivot index and j remain inside bounds
    invariant forall k | 0 <= k < lo || hi < k < a.Length :: a[k] == old(a[k]); // Other part of the array is untouched
    invariant a[hi] == pVal; // pivot value remains at the end of the array
    invariant forall k | lo <= k < pivot :: a[k] < pVal; // values before pivot are smaller
    invariant forall k | pivot <= k < j :: pVal <= a[k]; // values after pivot greater or equal
    invariant 0 < lo ==> Partitioned(a, 0, lo - 1, lo, hi); // first part of the array remains partitioned
    invariant hi < a.Length - 1 ==> Partitioned(a, lo, hi, hi + 1, a.Length - 1); // last part remains partitioned
  {
    if (a[j] < pVal) {
      swap(a, pivot, j);
      pivot := pivot + 1;
    }

    j := j + 1;
  }

  // Finally place the pivot at the correct index
  swap(a, pivot, hi);
}

/**
 * Sort the given array a[lo..hi] in ascending order.
 */
method Quicksort(a: array<int>, lo: int, hi: int)
  modifies a; // needed for arrays (since they are objects, not values such as sequences)
  requires 0 <= lo <= hi < a.Length; // lo and hi are within bounds
  requires 0 < lo ==> Partitioned(a, 0, lo - 1, lo, hi); // Assume that the first part of the array is partitioned
  requires hi < a.Length - 1 ==> Partitioned(a, lo, hi, hi + 1, a.Length - 1); // Assume last part is partitioned
  
  ensures forall k | 0 <= k < lo || hi < k < a.Length :: a[k] == old(a[k]); // Other part of the array is untouched
  ensures Sorted(a, lo, hi); // a[lo..hi] is sorted at the end
  ensures 0 < lo ==> Partitioned(a, 0, lo - 1, lo, hi); // first part of the array remains partitioned
  ensures hi < a.Length - 1 ==> Partitioned(a, lo, hi, hi + 1, a.Length - 1); // last part remains partitioned
  
  decreases hi-lo;
{
  if (lo == hi) {
    // Only one element to sort; we are done
    return;
  }

  // First partition the array and store the index of the pivot
  var pivot := Partition(a, lo, hi);

  if (pivot > lo) {
    // There are elements before the pivot; sort them
    Quicksort(a, lo, pivot - 1);
  } 

  if (pivot < hi) {
    // There are elements after the pivot; sort them
    Quicksort(a, pivot + 1, hi);
  } 
}

method PartitionTwoPivots(a: array<int>, lo: int, hi: int) returns (p1: int, p2: int)
  modifies a;

  requires 0 <= lo < hi < a.Length;

  ensures lo <= p1 < p2 <= hi;
  ensures a[p1] <= a[p2];
  ensures forall k | 0 <= k < lo || hi < k < a.Length :: a[k] == old(a[k]); // Ensure other part of array is untouched
  ensures forall k | lo <= k < p1 :: a[k] < a[p1]; // Ensure partitioning within lo..hi bounds
  ensures forall k | p1 <= k < p2 :: a[p1] <= a[k] < a[p2]; // Ensure partitioning within lo..hi bounds
  ensures forall k | p2 <= k <= hi :: a[p2] <= a[k]; // Ensure partitioning within lo..hi bounds
{
  if(a[lo] > a[hi]) {
    swap(a, lo, hi);
  }

  p1 := lo;
  p2 := hi;

  var p1Val := a[lo];
  var p2Val := a[hi];
  var j := lo + 1;

  while (j < p2) 
    decreases p2 - j;
    invariant lo <= p1 < j <= hi;
    invariant p1 < p2 <= hi;
    invariant forall k | 0 <= k < lo || hi < k < a.Length :: a[k] == old(a[k]); // Other part of the array is untouched
    invariant a[lo] == p1Val;
    invariant a[hi] == p2Val;
    invariant forall k | lo < k <= p1 :: a[k] < p1Val;
    invariant forall k | p1 <= k < j :: p1Val <= a[k] < p2Val;
  {
    if(a[j] < p1Val) {
      // assume (forall k | lo <= k < p1 :: a[k] < p1Val);
      p1 := p1 + 1;
      swap(a, j, p1);
      // assert (forall k | lo <= k < p1 :: a[k] < p1Val);
    } else if (a[j] >= p2Val) {
      p2 := p2 - 1;
      
      while (a[p2] > p2Val && j < p2) 
        decreases p2 - j;
        invariant p1 < p2;
        invariant j <= p2 <= hi;
      {
        p2 := p2 - 1;
      }

      assert (j <= p2);
      
      swap(a, j, p2);

      if (a[j] < p1Val) {
        p1 := p1 + 1;
        swap(a, j, p1);
      }

      assert (p1 < p2);

      assert (j <= p2);
    }

    j := j + 1;
  }

  swap(a, lo, p1);
  swap(a, hi, p2);

  assume false;
}

method Quickquicksort(a: array<int>, lo: int, hi: int)
  modifies a;
  requires 0 <= lo <= hi < a.Length;

  ensures forall k | 0 <= k < lo || hi < k < a.Length :: a[k] == old(a[k]); // Other part of the array is untouched
  ensures Sorted(a, lo, hi); // a[lo..hi] is sorted at the end
  decreases hi-lo;
{
  assume false;
}

/**
 * States that all elements in sub-array a[lo1..hi1] are smaller or equal than all elements in sub-array a[lo2..hi2].
 */
predicate Partitioned(a: array<int>, lo1: int, hi1: int, lo2: int, hi2: int)
  reads a;
  requires 0 <= lo1 <= hi1 <= lo2 <= hi2 < a.Length; // given integers must be within bounds of the array
{
  forall i,j | lo1 <= i <= hi1 < lo2 <= j <= hi2 :: a[i] <= a[j]
}

/**
 * States that the sub-array a[lo..hi] is sorted in ascending order.
 */
predicate Sorted(a:array<int>, lo: int, hi:int)
  reads a;
  requires 0 <= lo <= hi < a.Length; // lo and hi must be within bounds
{
  forall i | lo <= i < hi :: a[i] <= a[i+1]
}
