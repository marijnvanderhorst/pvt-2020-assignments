/**
 * 2IMP10, Program verification techniques, Assignment 2, Excercise 3.
 *
 * M. van der Horst (1000979 - m.v.d.horst@student.tue.nl)
 * T.M. Verberk (1016472 - t.m.verberk@student.tue.nl)
 */

/*
 * Finds the the index of the element key. 
 */
method Find(a: array<int>, key: int) returns (index: int)
   ensures 0 <= index ==> index < a.Length && a[index] == key // if the element is not zero make sure the index actually contains the key
{
    // initialize index
    index := 0;
    while index < a.Length
        invariant 0 <= index <= a.Length; // index is at least 0 and at most a.Length (+1 because loop)
        decreases a.Length-index; // a.Length - index is decreasing
    {
        if(a[index] == key){
            return;
        }
        index := index + 1;
    }
index := -1;
}


/*
 * Finds the the first index of the element key. 
 */
method FindPlus(a: array<int>, key: int) returns (index: int)
   ensures 0 <= index ==> index < a.Length && a[index] == key && forall k :: 0 <= k < index ==> a[k] != key //ensures that if we find an index all the indexes before the index don't have the key as element
   ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key // If we report -1 there is no index that has the key
{
    index := 0;
    while index < a.Length
        invariant 0 <= index <= a.Length;
        invariant forall k :: 0 <= k < index ==> a[k] != key
        decreases a.Length-index;
    {
        if(a[index] == key){
            return;
        }
        index := index + 1;
    }
    index := -1;
}


/*
 * Finds the the first and the last element of the element key. 
 */
method FindPlusPlus(a: array<int>, key: int) returns (indexlo: int, indexhi: int)
   ensures indexlo < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key // If we report -1 there is no index that has the key
   ensures indexhi < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key // If we report -1 there is no index that has the key
   ensures 0 <= indexhi ==> indexhi < a.Length && a[indexhi] == key && forall k :: indexhi < k < a.Length ==> a[k] != key //If we report a number it is the last index that has the key
   ensures 0 <= indexlo ==> indexlo < a.Length && a[indexlo] == key && forall j :: 0 < j < indexlo ==> a[j] != key //If we report a number it is the last index that has the key

{
    indexlo := -1;
    indexhi := -1;
    assert(0 <= indexhi ==> indexhi < a.Length && a[indexhi] == key);
    var index := 0;
    while index < a.Length
        invariant 0 <= index <= a.Length; // Index is bounded
        invariant -1 <= indexlo <= indexhi <= index <= a.Length; // Indexlo and indexHi are also bounded
        invariant indexlo <= indexhi < a.Length; //Indexlo is lower than indexHi
        invariant indexlo < 0 || indexhi < 0 ==> forall k :: 0 <= k < index ==> a[k] != key // If indexlo and indexhi give a value smaller than 0, the key is not in the array
        invariant 0 <= indexhi ==> indexhi < a.Length && a[indexhi] == key && forall k :: indexhi < k < index ==> a[k] != key //there is no index between indexhi and index that has the key as value
        invariant 0 <= indexlo ==> indexlo < a.Length && a[indexlo] == key && forall j :: 0 < j < indexlo ==> a[j] != key // there is no index before indexlo that has the key as value.
        decreases a.Length-index;
    {
        if(a[index] == key){
            indexhi := index;
            if(indexlo == -1){
                indexlo := index;
            }
        }
        index := index + 1;
    }
}


