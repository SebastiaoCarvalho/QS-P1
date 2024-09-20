datatype uop = Neg 
datatype bop = Plus | Minus 

datatype aexpr =
  Var(seq<nat>)
  | Val(nat)
  | UnOp(uop, aexpr)
  | BinOp(bop, aexpr, aexpr)
 
datatype code = 
  | VarCode(seq<nat>)  
  | ValCode(nat)       
  | UnOpCode(uop)      
  | BinOpCode(bop)     

function Serialize(a : aexpr) : seq<code> 
{
  match a {
    case Var(s) => [ VarCode(s) ]
    case Val(i) => [ ValCode(i) ]
    case UnOp(op, a1) => Serialize(a1) + [ UnOpCode(op) ]
    case BinOp(op, a1, a2) => Serialize(a2) + Serialize(a1) + [ BinOpCode(op) ]
  }
}


/*
  Ex1.1
*/
function Deserialize(cs : seq<code>) : seq<aexpr>
{
  DeserializeComplete(cs, [])
} 

function DeserializeComplete(cs : seq<code>, exps: seq<aexpr>) : seq<aexpr> 
{
  if (cs == []) then exps
  else DeserializeComplete(cs[1..], DeserializeAux(cs[0], exps))
}

function DeserializeAux(cd : code, exps : seq<aexpr>) : seq<aexpr>
{
  match cd {
    case VarCode(s) => [Var(s)] + exps
    case ValCode(i) => [Val(i)] + exps
    case UnOpCode(uop) => 
      if |exps| < 1 then []
      else [UnOp(uop, exps[0])] + exps[1..]
    case BinOpCode(bop) => 
      if |exps| < 2 then []
      else [BinOp(bop, exps[0], exps[1])] + exps[2..]
  }
}

/*
  Ex1.2
*/
lemma DeserializePropertyAux(e : aexpr, cs : seq<code>, exps: seq<aexpr>)
  ensures DeserializeComplete(Serialize(e) + cs, exps) == DeserializeComplete(cs, [ e ] + exps)
{
  match e {
    case Var(s) =>
      calc {
        DeserializeComplete(Serialize(e) + cs, exps);
        == DeserializeComplete(Serialize(Var(s)) + cs, exps);
        == DeserializeComplete([VarCode(s)] + cs, exps);
        == {assert ([VarCode(s)] + cs)[1..] == cs;} DeserializeComplete(cs, DeserializeAux(VarCode(s), exps));
        == DeserializeComplete(cs, [Var(s)] + exps);
      }
    case Val(i) =>
      calc {
        DeserializeComplete(Serialize(e) + cs, exps);
        == DeserializeComplete(Serialize(Val(i)) + cs, exps);
        == DeserializeComplete([ValCode(i)] + cs, exps);
        == {assert ([ValCode(i)] + cs)[1..] == cs;} DeserializeComplete(cs, DeserializeAux(ValCode(i), exps));
        == DeserializeComplete(cs, [Val(i)] + exps);
      }
    case UnOp(op, a1) =>
      calc {
        DeserializeComplete(Serialize(e) + cs, exps);
        == DeserializeComplete(Serialize(UnOp(op, a1)) + cs, exps);
        == DeserializeComplete(Serialize(a1) + [UnOpCode(op)] + cs, exps);
        == {assert Serialize(a1) + [UnOpCode(op)] + cs == Serialize(a1) + ([UnOpCode(op)] + cs); } 
        DeserializeComplete(Serialize(a1) + ([UnOpCode(op)] + cs), exps);
        == {DeserializePropertyAux(a1, [UnOpCode(op)] + cs, exps);} DeserializeComplete([UnOpCode(op)] + cs, [a1] + exps);
        == DeserializeComplete(cs, DeserializeAux(UnOpCode(op), [a1] + exps));
        == DeserializeComplete(cs, [UnOp(op, a1)] + exps);
        == DeserializeComplete(cs, [e] + exps);
      }
    case BinOp(op, a1, a2) =>
      calc {
        DeserializeComplete(Serialize(e) + cs, exps);
        == DeserializeComplete(Serialize(BinOp(op, a1, a2)) + cs, exps);
        == DeserializeComplete(Serialize(a2) + Serialize(a1) + [BinOpCode(op)] + cs, exps);
        == {assert Serialize(a2) + Serialize(a1) + [BinOpCode(op)] + cs == Serialize(a2) + (Serialize(a1) + [BinOpCode(op)] + cs); } 
        DeserializeComplete(Serialize(a2) + (Serialize(a1) + [BinOpCode(op)] + cs), exps);
        == {DeserializePropertyAux(a1, Serialize(a1) + [BinOpCode(op)] + cs, exps);}
        DeserializeComplete(Serialize(a1) + [BinOpCode(op)] + cs, [a2] + exps);
        == {assert Serialize(a1) + [BinOpCode(op)] + cs == Serialize(a1) + ([BinOpCode(op)] + cs);}
        DeserializeComplete(Serialize(a1) + ([BinOpCode(op)] + cs), [a2] + exps) ;
        == {DeserializePropertyAux(a1, [BinOpCode(op)] + cs, [a2] + exps);}
        DeserializeComplete([BinOpCode(op)] + cs, [a1] + ([a2] + exps));
        == {assert [a1] + ([a2] + exps) == [a1, a2] + exps;}
        DeserializeComplete([BinOpCode(op)] + cs, [a1, a2] + exps);
        == DeserializeComplete(cs, DeserializeAux(BinOpCode(op), [a1, a2] + exps));
        == DeserializeComplete(cs, [BinOp(op, a1, a2)] + exps);
        == DeserializeComplete(cs, [e] + exps);

      }
  }
}

lemma DeserializeProperty(e : aexpr)
  ensures Deserialize(Serialize(e)) == [e]
{
  calc {
    Deserialize(Serialize(e));
    == {assert Serialize(e) + [] == Serialize(e);} DeserializeComplete(Serialize(e) + [], []);
    == {DeserializePropertyAux(e, [], []);} DeserializeComplete([], [e] + []);
    == DeserializeComplete([], [e]);
    == [e];
  }
}

/*
  Ex1.3
*/
function SerializeCodes(cs : seq<code>) : seq<nat> 
{
  SerializeCodesComplete(cs, [])
}

function SerializeCodesComplete(cs : seq<code>, exprs : seq<nat>) : seq<nat>
{
  if (|cs| == 0) then exprs
  else SerializeCodesComplete(cs[1..], SerializeCodesAux(cs[0], exprs))
}

function SerializeCodesAux(c : code, exprs : seq<nat>) : seq<nat>
{
  match c {
    case VarCode(s) => [0] + [|s|] + s + exprs
    case ValCode(i) => [1, i] + exprs
    case UnOpCode(uop) => SerializeUop(uop) + exprs
    case BinOpCode(bop) => SerializeBop(bop) + exprs
  }
}

function SerializeUop(op : uop) : seq<nat>
{
  [2]
}

function SerializeBop(op : bop) : seq<nat>
{
  match op {
    case Plus => [3, 0]
    case Minus => [3, 1]
  }
}

function DeserializeCodes(ints : seq<nat>) : seq<code> 
{
  DeserializeCodesComplete(ints, [])
}

function DeserializeCodesComplete(ints : seq<nat>, exprs : seq<code>) : seq<code> 
{
  if (|ints| == 0) then exprs
  else match ints[0] {
      case 0 => if (|ints| < 2) then []
                else if (|ints| < 2 + ints[1]) then []
                else DeserializeCodesComplete(ints[(2 + ints[1])..], [VarCode(ints[2..(2 + ints[1])])] + exprs)
      case 1 => if (|ints| < 2) then []
                else DeserializeCodesComplete(ints[2..], [ValCode(ints[1])] + exprs)
      case 2 => DeserializeCodesComplete(ints[1..], [UnOpCode(Neg)] + exprs)
      case 3 => if (|ints| < 2) then []
                else DeserializeCodesComplete(ints[2..], DeserializeBop(ints[..2]) + exprs)
      case _ => []
  }
}

function DeserializeBop(nums : seq<nat>) : seq<code>
{
  if (|nums| < 2) then []
  else match nums[1] {
    case 0 => [BinOpCode(Plus)]
    case 1 => [BinOpCode(Minus)]
    case _ => []
  }
}

function DeserializeCodeVar(ints : seq<nat>, exprs : seq<code>) : seq<code>
{
  if (|ints| < 2) then []
  else if (|ints| < 2 + ints[1]) then []
  else DeserializeCodesComplete(ints[(2 + ints[1])..], [VarCode(ints[2..(2 + ints[1])])] + exprs)
}

function DeserializeCodeVal(ints : seq<nat>, exprs : seq<code>) : seq<code>
{
  if (|ints| < 2) then []
  else DeserializeCodesComplete(ints[2..], [ValCode(ints[1])] + exprs)
}
/*
  Ex1.4
*/
lemma DeserializeCodesProperty(cs : seq<code>)
  ensures DeserializeCodes(SerializeCodes(cs)) == cs
{
  calc {
    DeserializeCodes(SerializeCodes(cs));
    == DeserializeCodesComplete(SerializeCodes(cs), []);
    == DeserializeCodesComplete(SerializeCodesComplete(cs, []), []);
    == {DeserializeCodesPropertyAux(cs, [], []);} DeserializeCodesComplete([], cs + []);
    == cs + [];
    == cs;
  }
}

lemma DeserializeCodesPropertyAux(cs : seq<code>, exprs : seq<nat>, exprs2 : seq<code>)
  ensures DeserializeCodesComplete(SerializeCodesComplete(cs, exprs), exprs2) == DeserializeCodesComplete(exprs, cs + exprs2) 
{
  if (|cs| == 0) {
    calc {
      DeserializeCodesComplete(SerializeCodesComplete(cs, exprs), exprs2);
      == DeserializeCodesComplete(SerializeCodesComplete([], exprs), exprs2);
      == DeserializeCodesComplete(exprs, exprs2);
      == {assert [] + exprs2 == exprs2;} DeserializeCodesComplete(exprs, [] + exprs2);
      == DeserializeCodesComplete(exprs, cs + exprs2);
    }
  }
  else {
    match cs[0] {
      case VarCode(s) => calc {
        DeserializeCodesComplete(SerializeCodesComplete(cs, exprs), exprs2);
        == DeserializeCodesComplete(SerializeCodesComplete(cs[1..], SerializeCodesAux(cs[0], exprs)), exprs2);
        == DeserializeCodesComplete(SerializeCodesComplete(cs[1..], SerializeCodesAux(VarCode(s), exprs)), exprs2);
        == DeserializeCodesComplete(SerializeCodesComplete(cs[1..], [0] + [|s|] + s + exprs), exprs2);
        == {DeserializeCodesPropertyAux(cs[1..], [0] + [|s|] + s + exprs, exprs2);} DeserializeCodesComplete([0] + [|s|] + s + exprs, cs[1..] + exprs2);
        == DeserializeCodesComplete([0, |s|] + s + exprs, cs[1..] + exprs2);
        == DeserializeCodesComplete(exprs, [VarCode(s)] + cs[1..] + exprs2);
        == {assert [VarCode(s)] + cs[1..] == cs;} DeserializeCodesComplete(exprs, cs + exprs2);
      }
      case ValCode(i) => calc {
        DeserializeCodesComplete(SerializeCodesComplete(cs, exprs), exprs2);
        == DeserializeCodesComplete(SerializeCodesComplete(cs[1..], SerializeCodesAux(cs[0], exprs)), exprs2);
        == DeserializeCodesComplete(SerializeCodesComplete(cs[1..], SerializeCodesAux(ValCode(i), exprs)), exprs2);
        == DeserializeCodesComplete(SerializeCodesComplete(cs[1..], [1, i] + exprs), exprs2);
        == {DeserializeCodesPropertyAux(cs[1..], [1,i] + exprs, exprs2);} DeserializeCodesComplete(([1,i] + exprs), cs[1..] + exprs2);
        == {assert ([1,i] + exprs)[0] == 1;} {assert |([1,i] + exprs)| >= 2;}
        DeserializeCodesComplete(([1,i] + exprs)[2..], [ValCode(([1,i] + exprs)[1])] + cs[1..] + exprs2);
        == {assert i == ([1,i] + exprs)[1];} {assert 1 == ([1,i] + exprs)[0];} {assert exprs == ([1,i] + exprs)[2..];}
        DeserializeCodesComplete(exprs, [ValCode(i)] + cs[1..] + exprs2);
        == {assert [ValCode(i)] + cs[1..] == cs;} DeserializeCodesComplete(exprs, cs + exprs2);
      }
      case UnOpCode(uop) => calc {
        DeserializeCodesComplete(SerializeCodesComplete(cs, exprs), exprs2);
        == DeserializeCodesComplete(SerializeCodesComplete(cs[1..], SerializeCodesAux(cs[0], exprs)), exprs2);
        == DeserializeCodesComplete(SerializeCodesComplete(cs[1..], SerializeCodesAux(UnOpCode(uop), exprs)), exprs2);
        == DeserializeCodesComplete(SerializeCodesComplete(cs[1..], SerializeUop(uop) + exprs), exprs2);
        == {DeserializeCodesPropertyAux(cs[1..], SerializeUop(uop) + exprs, exprs2);} DeserializeCodesComplete(SerializeUop(uop) + exprs, cs[1..] + exprs2);
        == DeserializeCodesComplete([2] + exprs, cs[1..] + exprs2);
        == DeserializeCodesComplete(exprs, [UnOpCode(uop)] + cs[1..] + exprs2);
        == {assert [UnOpCode(uop)] + cs[1..] == cs;} DeserializeCodesComplete(exprs, cs + exprs2);
      }
      case BinOpCode(bop) => calc {
        DeserializeCodesComplete(SerializeCodesComplete(cs, exprs), exprs2);
        == DeserializeCodesComplete(SerializeCodesComplete(cs[1..], SerializeCodesAux(cs[0], exprs)), exprs2);
        == DeserializeCodesComplete(SerializeCodesComplete(cs[1..], SerializeCodesAux(BinOpCode(bop), exprs)), exprs2);
        == DeserializeCodesComplete(SerializeCodesComplete(cs[1..], SerializeBop(bop) + exprs), exprs2);
        == {DeserializeCodesPropertyAux(cs[1..], SerializeBop(bop) + exprs, exprs2);} DeserializeCodesComplete(SerializeBop(bop) + exprs, cs[1..] + exprs2);
        == {assert SerializeBop(bop)[0] == 3;} DeserializeCodesComplete(exprs, DeserializeBop(SerializeBop(bop)) + cs[1..] + exprs2);
        == {assert [BinOpCode(bop)] + cs[1..] == cs;} DeserializeCodesComplete(exprs, cs + exprs2);
      }
    }
  }
}

/*
  Ex1.5
*/
function FullSerialize(e : aexpr) : seq<nat> {
  SerializeCodes(Serialize(e))
}

function FullDeserealize(nats : seq<nat>) : seq<aexpr> {
  Deserialize(DeserializeCodes(nats))
}

/*
  Ex1.6
*/
lemma FullDeserealizeProperty(e : aexpr)
  ensures FullDeserealize(FullSerialize(e)) == [ e ]
{
  calc {
    FullDeserealize(FullSerialize(e));
    == Deserialize(DeserializeCodes(SerializeCodes(Serialize(e))));
    == {DeserializeCodesProperty(Serialize(e));} Deserialize(Serialize(e));
    == {DeserializeProperty(e);} [ e ];
  }    
}