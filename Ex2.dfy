function noRepetitionF(arr : seq<nat>) : bool
{
  if (|arr| == 0) then true
  else if (existsInArray(arr[1..], arr[0])) then false
  else noRepetitionF(arr[1..])
}

function existsInArray(arr : seq<nat>, v : nat) : bool
{
  if (|arr| == 0) then false
  else if (arr[0] == v) then true
  else existsInArray(arr[1..], v)
}

method noRepetitionsQuadratic(arr : array<nat>) returns (b: bool) 
ensures b == noRepetitionF(arr[..])
{
  var i := 0; 
  b := true; 

  while (i < arr.Length)
  invariant 0 <= i <= arr.Length
  invariant b == noRepetitionF(arr[i..])
  {

    var v := arr[i];   
    var j := 0;
  
    while (j < arr.Length) 
    invariant 0 <= j <= arr.Length
    {
      var u := arr[j]; 
      if ((j != i) && (u == v)) {
        b := false; 
        return; 
      }
      j := j+1;
    }
    i := i+1; 
  }
}




method noRepetitionsLinear(arr : array<nat>) returns (b: bool) 
{

}
