
module Ex3 {


class Node {

  var data : int 
  var next : Node? 

  ghost var list : seq<int>
  ghost var footprint : set<Node>

  ghost function Valid() : bool 
    reads this, footprint
    decreases footprint
  {
    (this in footprint) &&
    ((next == null) ==> list == [ data ] && footprint == { this }) &&
    ((next != null) ==> 
      (next in footprint) && 
      footprint == next.footprint + { this } && 
      (this !in next.footprint) &&
      list == [ data ] + next.list &&
      next.Valid())
  }

  constructor (val : int) 
    ensures Valid() 
      && next == null && list == [ data ] 
      && footprint == { this } 
      && val == data 
  {
    this.data := val; 
    this.next := null; 
    this.list := [ val ]; 
    this.footprint := { this };
  } 

  method prepend (val : int) returns (r : Node)
    requires Valid()
    ensures r.Valid()
    ensures r.list == [ val ] + this.list
    ensures r.footprint == { r } + this.footprint
    ensures fresh(r) 
  {
    r := new Node(val); 
    r.next := this; 
    r.footprint := { r } + this.footprint; 
    r.list := [ val ] + this.list;  
    return; 
  }


  method reverse(tail : Node?) returns (r : Node)
    //requires 
    requires this.Valid()
    requires tail != null ==> tail.Valid()
    requires tail != null ==> this.footprint !! tail.footprint

    //list
    ensures tail == null ==> r.list == reverseList(old(this.list))
    ensures tail != null ==> r.list == reverseList(old(this.list)) + old(tail.list)

    //Valid 
    ensures this.Valid()
    ensures r.Valid()

    modifies this.next ,this.footprint
    decreases footprint 
  {

    var old_next := this.next; 
    this.next := tail;

    if (old_next == null) {
      if (tail != null) {
        this.list := [this.data] + tail.list;
        this.footprint := { this } + tail.footprint;
      }
      else {
        this.list := [this.data];
        this.footprint := { this };
      }
      r := this;
      return; 
    } else {
      if (tail != null) {
        this.list := [this.data] + tail.list;
        this.footprint := { this } + tail.footprint;
      }
      else {
        this.list := [this.data];
        this.footprint := { this };
      }
      r := old_next.reverse(this);
      return;
    }
  }


}

  // Ex2
  method ExtendList(nd : Node?, v : int) returns (r : Node)
    requires nd != null ==> nd.Valid()
    ensures r.Valid()
    ensures fresh(r)
  {
    if (nd == null) {
      r := new Node(v);
      return;
    }
    else {
      r := nd.prepend(v);
      return;
    }
  }

  function reverseList(lst: seq<int>) : seq<int>
    decreases |lst|
    {
    if |lst| == 0 then []
    else reverseList(lst[1..]) + [lst[0]]
    }


}

