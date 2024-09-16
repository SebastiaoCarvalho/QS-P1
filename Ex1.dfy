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
function Deserialize(cs : seq<code>, exps: seq<aexpr>) : seq<aexpr> 
{
  if (cs == []) then []
  else Deserialize(cs[1..], DeserializeAux(cs[0], exps))
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
lemma DeserializeProperty(e : aexpr, cs : seq<code>, exps: seq<aexpr>)
  ensures Deserialize(Serialize(e) + cs, exps) == Deserialize(cs, [ e ] + exps)
{
  match e {
    case Var(s) =>
      calc {
        Deserialize(Serialize(e) + cs, exps);
        == Deserialize(Serialize(Var(s)) + cs, exps);
        == Deserialize([VarCode(s)] + cs, exps);
        == {assert ([VarCode(s)] + cs)[1..] == cs;} Deserialize(cs, DeserializeAux(VarCode(s), exps));
        == Deserialize(cs, [Var(s)] + exps);
      }
    case Val(i) =>
      calc {
        Deserialize(Serialize(e) + cs, exps);
        == Deserialize(Serialize(Val(i)) + cs, exps);
        == Deserialize([ValCode(i)] + cs, exps);
        == {assert ([ValCode(i)] + cs)[1..] == cs;} Deserialize(cs, DeserializeAux(ValCode(i), exps));
        == Deserialize(cs, [Val(i)] + exps);
      }
    case UnOp(op, a1) =>
      calc {
        
      }
  }
}


/*
  Ex1.3
*/
/*function SerializeCodes(cs : seq<code>) : seq<nat> 
{

}

function DeserializeCodes(ints : seq<nat>) : seq<code> {
  
}*/


/*
  Ex1.4
*/
/*lemma DeserializeCodesProperty(cs : seq<code>)
  ensures DeserializeCodes(SerializeCodes(cs)) == cs
{
}*/

/*
  Ex1.5
*/
/*function FullSerialize(e : aexpr) : seq<nat> {
 
}

function FullDeserealize(nats : seq<nat>) : seq<aexpr> {
 
}*/

/*
  Ex1.6
*/
/*lemma FullDeserealizeProperty(e : aexpr)
  ensures FullDeserealize(FullSerialize(e)) == [ e ]
{
    
}*/