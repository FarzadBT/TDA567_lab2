class Sorting {
    predicate sorted(ints : seq<int>) {
        forall i,j :: 0 <= i < j < |ints| ==> ints[i] < ints[j]
    }
}