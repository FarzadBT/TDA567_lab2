// A LIFO queue (aka a stack) with limited capacity.
class LimitedStack{

      var capacity : int; // capacity, max number of elements allowed on the stack.
      var arr : array?<int>; // contents of stack.
      var top : int; // The index of the top of the stack, or -1 if the stack is empty

      // This predicate express a class invariant: All objects of this calls should satisfy this.
      predicate Valid()
      reads this;
      {
          arr != null && capacity > 0 && capacity == arr.Length && top >= -1 && top < capacity
      }

      predicate Empty()
      reads this;
      {
          top == -1
      }

      predicate Full()
      reads this;
      {
          top == capacity - 1
      }

      method Init(c : int)
      modifies this;
      requires c > 0;

      ensures fresh(arr); // ensures arr is a newly created object.
      ensures Valid();
      ensures Empty();

      {
        capacity := c;
        arr := new int[c];
        top := -1;
      }

     
      method isEmpty() returns (res : bool)
      requires Empty();
      {
            res := true;
      }


      // Returns the top element of the stack, without removing it.
      method Peek() returns (elem : int)
      requires Valid();
      requires !Empty();
      {
          elem := arr[top];
      }

      // Pushed an element to the top of a (non full) stack. 
      method Push(elem : int)
      requires Valid() && !Full();

      ensures !Empty() && Valid();
    
      modifies this.arr, this`top;
      {
          top := top + 1;
          arr[top] := elem;
      }

      // Pops the top element off the stack.
      method Pop() returns (elem : int)
        requires Valid() && !Empty();

        ensures !Full() && Valid();

        modifies this`top;
      {
          elem := arr[top];
          top := top-1;
      }
 
      method Shift()
      requires Valid() && !Empty();
      ensures Valid();
      ensures forall i : int :: 0 <= i < capacity - 1 ==> arr[i] == old(arr[i + 1]);
      ensures top == old(top) - 1;
      modifies this.arr, this`top;
      {
        var i : int := 0;
        while (i < capacity - 1 )
        invariant 0 <= i < capacity;
        invariant top == old(top);
        invariant forall j : int :: 0 <= j < i ==> arr[j] == old(arr[j + 1]);
        invariant forall j : int :: i <= j < capacity ==> arr[j] == old(arr[j]);
        {
          arr[i] := arr[i + 1];
          i := i + 1;
        }
        top := top - 1;
      }

      //Push onto full stack, oldest element is discarded.
      method Push2(elem : int)
      requires Valid();

      modifies this.arr, this`top;
      {
            if(top == capacity-1) {
                Shift();
            }
            top := top+1;
            arr[top] := elem;
      }


// When you are finished,  all the below assertions should be provable. 
// Feel free to add extra ones as well.
      method Main(){
           var s := new LimitedStack;
           s.Init(3);

           assert s.Empty() && !s.Full(); 

           s.Push(27);
           assert !s.Empty();

           var e := s.Pop();
           assert e == 27;

           s.Push(5);
           s.Push(32);
           s.Push(9);
           assert s.Full();

           var e2 := s.Pop();
           assert e2 == 9 && !s.Full(); 
           assert s.arr[0] == 5;

           s.Push(e2);
           s.Push2(99);

           var e3 := s.Peek();
           assert e3 == 99;
           assert s.arr[0] == 32;
                     
       }
}
