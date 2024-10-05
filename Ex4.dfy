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
    modifies this
    ensures Valid()
    ensures this.content == {v} + old(this.content)
    ensures this.footprint >= old(this.footprint)
    ensures fresh(this.footprint - old(this.footprint))
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
          this.list := n;
          this.content := {v} + this.content;
          this.footprint := {n} + this.footprint;
        }
      }
    }


    method union(s : Set) returns (r : Set)
    requires Valid() && s.Valid()
    ensures fresh(r) && r.Valid()
    ensures r.content == s.content + this.content
    {
      r := new Set();
      var cur1 := this.list;
      ghost var list_aux : set<nat> := {};
      while (cur1 != null)
      invariant r.Valid()
      invariant cur1 != null ==> cur1.Valid()
      invariant r.content == list_aux
      invariant cur1 != null ==> this.content == list_aux + cur1.content
      invariant cur1 == null ==> list_aux == this.content
      decreases if cur1 != null then cur1.footprint else {}
      {
        r.add(cur1.val);
        list_aux := list_aux + {cur1.val};
        cur1 := cur1.next;
      }
      var cur2 := s.list;
      ghost var list_aux2 : set<nat> := {};
      while (cur2 != null)
      invariant r.Valid()
      invariant r.content == list_aux2 + this.content
      invariant cur2 != null ==> cur2.Valid()
      invariant cur2 != null ==> s.content == list_aux2 + cur2.content
      invariant cur2 == null ==> list_aux2 == s.content
      decreases if cur2 != null then cur2.footprint else {}
      {
        r.add(cur2.val);
        list_aux2 := list_aux2 + {cur2.val};
        cur2 := cur2.next;
      }
    }


  method inter(s : Set) returns (r : Set)
  requires Valid() && s.Valid()
  ensures fresh(r) && r.Valid()
  ensures r.content == s.content * this.content
    {
      r := new Set();
      var cur1 := this.list;
      ghost var list_aux : set<nat> := {};
      while (cur1 != null)
      invariant r.Valid()
      invariant cur1 != null ==> cur1.Valid()
      invariant r.content == list_aux * s.content
      invariant (cur1 != null) ==> (this.content == list_aux + cur1.content)
      invariant (cur1 == null) ==> (list_aux == this.content)
      decreases if cur1 != null then cur1.footprint else {}
      {
        var condition := s.mem(cur1.val);
        if (condition) {
          r.add(cur1.val);
        }
        list_aux := list_aux + {cur1.val};

        cur1 := cur1.next;
      }
    }
  }

}

