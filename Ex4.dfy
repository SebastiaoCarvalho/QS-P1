include "Ex3.dfy"

module Ex4 {
  import Ex3=Ex3

  class Set {
    var list : Ex3.Node?

    ghost var footprint : set<Ex3.Node>
    ghost var content : set<nat>

    ghost function Valid() : bool 
      reads this, footprint, this.list
    {
      if (this.list == null)
        then 
          footprint == {}
          &&
          content == {}
        else 
          footprint == list.footprint
          &&
          content == list.content
          &&
          list.Valid()
    }

    constructor () 
      ensures Valid() && this.content == {} && this.footprint == {}
    {
      list := null; 
      footprint := {}; 
      content := {};      
    }


    method mem (v : nat) returns (b : bool)
    requires Valid()
    ensures b == (v in content)
    {
      if (list == null) {
        b := false;
        return;
      }
      b := list.mem(v);
      return;
    }


    method add (v : nat)
    requires Valid()
    modifies this, footprint
    ensures Valid()
    ensures this.content == {v} + old(this.content)
    ensures this.footprint >= old(this.footprint) 
    {
      if (this.list == null) {
        var n := new Ex3.Node(v);
        this.list := n;
        this.content := {v};
        this.footprint := {n};
      }
      else {
        var condition := this.list.mem(v);
        if (! condition) {
          var n := this.list.add(v);
          this.content := {v} + this.content;
          this.footprint := {n} + this.footprint;
        }
      }
    }


    method union(s : Set) returns (r : Set)
    requires Valid() && s.Valid()
    decreases footprint
    ensures forall k :: (k in r.content) ==> ((k in s.content) || (k in this.content))
    {
      
    }


  method inter(s : Set) returns (r : Set)
  requires Valid() && s.Valid()
  ensures fresh(r)
  ensures forall k :: (k in r.content) <==> ((k in s.content) && (k in this.content))
    {
      r := new Set();
      var cur1 := this.list;
      while (cur1 != null)
      invariant r.Valid()
      decreases if cur1 != null then cur1.footprint else {}
      {
        var condition := s.mem(cur1.val);
        if (condition) {
          r.add(cur1.val);
        }
        cur1 := cur1.next;
      }
    }
  }

}

