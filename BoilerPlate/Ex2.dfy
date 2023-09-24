function sorted(s : seq<int>) : bool {
  forall k1, k2 :: 0 <= k1 <= k2 < |s| ==> s[k1] <= s[k2]
}


// Ex1
method copy(a : array<int>, l : int, r : int) returns (ret : array<int>)
  requires 0 <= l < r <= a.Length 
  ensures ret[..] == a[l..r]
{
  var len := r - l; // Calculate the length of the ret.
  ret := new int[len];  // Create the array ret with len
  var i := 0;

  while (i < len)
    invariant 0 <= i <= len 
    invariant forall k :: 0 <= k < i ==> ret[k] == a[l + k] // 'ret' should contain copied elements
    decreases len - i 
  {
    
    ret[i] := a[l + i]; // Copy the element from 'a' to 'ret' at the current index.
    i := i + 1;
  }
}


// Ex2

method mergeArr(a : array<int>, l : int, m : int, r : int) 
  requires 0 <= l < m < r <= a.Length  
  requires sorted(a[l..m]) && sorted(a[m..r])
  ensures sorted(a[l..r]) 
  ensures a[..l] == old(a[..l])
  ensures a[r..] == old(a[r..]) 
  modifies a 
{
 // ToDo 
}


// Ex3
method sort (a : array<int>) 
  ensures sorted(a[..])
  modifies a 
{
  // ToDo
}





