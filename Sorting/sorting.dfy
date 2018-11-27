class Sorting {
    predicate sorted(ints : seq<int>) {
        forall i :: 0 < i < |ints| ==> ints[i-1] < ints[i]
    }

    predicate sorted'(ints : seq<int>) {
        forall i :: |ints| > i > 0 ==> ints[i] > ints[i-1]
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

    ghost method sorted'ifsorted(ints : seq<int>)
        requires sorted(ints)
        ensures sorted'(ints)
    {

    }

    ghost method sortedifsorted'(ints : seq<int>)
        requires sorted'(ints)
        ensures sorted(ints)
    {

    }

    method Main() {
        assert multiset({1, 1, 2}) == multiset{1, 2};
        assert multiset([1, 1, 2]) == multiset([1, 2, 1]);

        var m := map[];
        m := m[1 := 3];
        m := m[1 := m[1]+1];
        assert m[1] == 4;
    }
}