class Sorting {
    predicate sorted1(ints : seq<int>) {
        forall i :: 0 <= i < |ints| - 1 ==> ints[i] < ints[i+1]
    }

    predicate sorted2(ints : seq<int>) {
        forall i,j :: 0 <= i < j < |ints| ==> ints[i] <= ints[j]
    }

    predicate p(a : seq<int>, b : seq<int>) {
        multiset(a) == multiset(b)
    }

    predicate p'(a : seq<int>, b : seq<int>) {
        forall v :: count(a, v) == count(b, v)
    }

    function count(a: seq<int>, v: int): int 
    decreases  a, v
    {
        if (|a| > 0) then
            if (a[0] == v) then 1 + count(a[1..], v)
            else count(a[1..], v)
        else 0
    }

    lemma sorted2IfSorted1(ints : seq<int>)
        requires sorted1(ints)
        ensures sorted2(ints)
    {
        
    }

    lemma sorted1IfSorted2(ints : seq<int>)
        requires sorted1(ints)
        ensures sorted2(ints)
    {

    }

    /*method sort(arr : array<int>) 
        requires arr.Length >= 2;
        ensures p(arr[..], old(arr[..]));
        ensures sorted(arr[..]);
    {
        
    }*/

    // Question about why the invariant don't work
    // From a quick  glance at the lab session it looked like it should work.
    method sortUnderSpecified(arr : array<int>) 
        requires arr != null;
        requires arr.Length >= 2;
        ensures sorted1(arr[..]);

        modifies arr;
    {
        var l := arr.Length;
        var z := 0;
        while (z < l)
            decreases  l - z
            
            invariant 0 <= z <= l;
            invariant forall k :: 0 <= k <= z ==> arr[k] <= arr[z];
        {
            arr[z] := z;
            z := z + 1;
        }
    }
}