include "Ex3.dfy"

module Ex4 {

import Ex3=Ex3

class Queue {

  var lst1 : Ex3.Node?
  var lst2 : Ex3.Node?

  ghost var footprint : set<Ex3.Node>

  // Ex1
  ghost function Valid() : bool
    
  {
    // ToDo
    lst1.Valid();
    lst2.Valid();
    // check the general footprint / list
  }

  // Ex2 
  constructor () 
  {
    this.lst1 := null; 
    this.lst2 := null;  
    // ToDo
    this.list := []; 
    this.footprint := {};
  }

  // Ex3.1
  method push(val : int) 
  {
    lst1 := Ex3.ExtendList(lst1, val);
    this.list := this.list + [val];
    this.footprint := this.footprint + {lst1.footprint - old(lst1.footprint)};
  }

  // Ex3.2
  method pop() returns (r : int)
  {

    if (lst2 == null) {
      lst2 := lst1.reverse(null); 
      lst1 := null;
    }

    r := lst2.data; 
    lst2 := lst2.next; 
  }
  
}

}