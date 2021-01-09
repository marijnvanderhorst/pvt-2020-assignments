method Find(a: array<int>, key: int) returns (index: int)
   ensures 0 <= index ==> index < a.Length && a[index] == key
{
    index := 0;
    while index < a.Length
        invariant 0 <= index <= a.Length;
        decreases a.Length-index;
    {
        if(a[index] == key){
            return;
        }
        index := index + 1;
    }
index := -1;
}

method FindPlus(a: array<int>, key: int) returns (index: int)
   ensures 0 <= index ==> index < a.Length && a[index] == key && forall k :: 0 <= k < index ==> a[k] != key
   ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
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

method FindPlusPlus(a: array<int>, key: int) returns (indexlo: int, indexhi: int)
   ensures indexlo < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
   ensures indexhi < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
   ensures 0 <= indexhi ==> indexhi < a.Length && a[indexhi] == key && forall k :: indexhi < k < a.Length ==> a[k] != key
   ensures 0 <= indexlo ==> indexlo < a.Length && a[indexlo] == key && forall j :: 0 < j < indexlo ==> a[j] != key

{
    indexlo := -1;
    indexhi := -1;
    assert(0 <= indexhi ==> indexhi < a.Length && a[indexhi] == key);
    var index := 0;
    while index < a.Length
        invariant 0 <= index <= a.Length;
        invariant -1 <= indexlo <= indexhi <= index <= a.Length;
        invariant indexlo <= indexhi < a.Length;
        invariant indexlo < 0 || indexhi < 0 ==> forall k :: 0 <= k < index ==> a[k] != key
        invariant 0 <= indexhi ==> indexhi < a.Length && a[indexhi] == key && forall k :: indexhi < k < index ==> a[k] != key
        invariant 0 <= indexlo ==> indexlo < a.Length && a[indexlo] == key && forall j :: 0 < j < indexlo ==> a[j] != key
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


