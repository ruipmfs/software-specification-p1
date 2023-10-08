include "Ex3.dfy"

module Ex4 {

import Ex3=Ex3

class Queue {
  var lst1 : Ex3.Node?
  var lst2 : Ex3.Node?

  ghost var footprint : set<Ex3.Node>

  // Ex1
  ghost function Valid() : bool
    reads this, footprint, lst1, lst2
    decreases footprint
  {
    (lst1 == null && lst2 == null ==> footprint == {}) &&
    (lst1 != null && lst2 != null ==>
      footprint == (lst1.footprint + lst2.footprint) && 
      lst1.Valid() && 
      lst2.Valid() && 
      (lst1.footprint !! lst2.footprint) &&
      lst1.list + lst2.list == []
    ) &&
    (lst1 == null && lst2 != null ==> 
      footprint == lst2.footprint &&
      lst2.Valid() &&
      lst2.list == []
    ) &&
    (lst1 != null && lst2 == null ==>
      footprint == lst1.footprint &&
      lst1.Valid() &&
      lst1.list == []
    )
  }

  // Ex2 
  constructor () 
  {
    this.lst1 := null; 
    this.lst2 := null;
    this.footprint := {};
  }

  // Ex3.1
  method push(val : int)
    requires lst1 != null ==> lst1.Valid()
    requires Valid()
    ensures lst1 != null ==> lst1.Valid()
    //ensures Valid()
    modifies lst1, this, footprint
  {
    lst1 := Ex3.ExtendList(lst1, val);
    if (old(lst1) == null) {
      this.footprint := this.footprint + lst1.footprint;
    }
    else {    
      this.footprint := this.footprint + (lst1.footprint - old(lst1.footprint));
    }
  }

  // Ex3.2
  method pop() returns (r : int)
    requires Valid()
    requires lst2 != null ==> lst2.Valid()
    requires lst2 == null ==> lst1 != null && lst1.Valid()
    ensures Valid()
    ensures lst2 != null ==> lst2.Valid()
    modifies this, footprint, lst2, lst1
  {
    if (lst2 == null) {
      lst2 := lst1.reverse(null); 
      lst1 := null;
      this.footprint := this.lst2.footprint;
    }

    r := lst2.data;
    if (lst2.next != null) {
      this.footprint := this.footprint - (lst2.footprint - lst2.next.footprint);
    }
    else {
      this.footprint := this.footprint - lst2.footprint;
    }
    lst2 := lst2.next;
  }
}

}