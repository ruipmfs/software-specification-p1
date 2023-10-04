datatype Tree<V> = Leaf(V) | SingleNode(V, Tree<V>) | DoubleNode(V, Tree<V>, Tree<V>)

datatype Code<V> = CLf(V) | CSNd(V) | CDNd(V)

function serialise<V>(t : Tree<V>) : seq<Code<V>> 
  decreases t 
{
  match t {
    case Leaf(v) => [ CLf(v) ]
    case SingleNode(v, t) => serialise(t) + [ CSNd(v) ]
    case DoubleNode(v, t1, t2) => serialise(t2) + serialise(t1) + [ CDNd(v) ]
  }
}

// Ex 1
function deserialiseAux<T>(codes: seq<Code<T>>, trees: seq<Tree<T>>): seq<Tree<T>>
  requires |codes| > 0 || |trees| > 0
  ensures |deserialiseAux(codes, trees)| >= 0
  decreases codes
{
  if |codes| == 0 then trees
  else
    match codes[0] {
      case CLf(v) => deserialiseAux(codes[1..], trees + [Leaf(v)])
      case CSNd(v) => if (|trees| >= 1) then deserialiseAux(codes[1..], trees[..|trees|-1] + [SingleNode(v, trees[|trees|-1])]) else trees
      case CDNd(v) => if (|trees| >= 2) then deserialiseAux(codes[1..], trees[..|trees|-2] + [DoubleNode(v, trees[|trees|-1], trees[|trees|-2])]) else trees
    }
}

function deserialise<T>(s:seq<Code<T>>):seq<Tree<T>>
  requires |s| > 0
{
  deserialiseAux(s, [])
}

// Ex 2
method testSerializeWithASingleLeaf()
{
  var tree := Leaf(42);
  var result := serialise(tree);
  assert result == [CLf(42)];
}

method testSerializeNullValues()
{
    var tree := Leaf(null);
    var result := serialise(tree);
    assert result == [CLf(null)];
}

method testSerializeWithAllElements()
{
  var tree: Tree<int> := DoubleNode(9, Leaf(6), DoubleNode(2, Leaf(5), SingleNode(4, Leaf(3))));
  var codes := serialise(tree);
  assert |codes| == 6;
  var expectedCodes := [CLf(3), CSNd(4), CLf(5), CDNd(2), CLf(6), CDNd(9)];
  assert codes == expectedCodes;
}

// Ex 3 

method testDeseraliseWithASingleLeaf() {
  var codes: seq<Code<int>> := [CLf(9)];
  var trees := deserialise(codes);
  assert |trees| == 1;
  var expectedTree := Leaf(9);
  assert trees[0] == expectedTree;
}

method testDeserializeWithASingleNode()
{
  var codes: seq<Code<int>> := [CLf(3), CSNd(9)];
  var trees := deserialise(codes);
  assert |trees| == 1;
  var expectedTree := SingleNode(9, Leaf(3));
  assert trees[0] == expectedTree;
}

method testDeserialiseWithAllElements()
{
    var codes: seq<Code<int>> := [CLf(3), CSNd(4), CLf(5), CDNd(2), CLf(6), CDNd(9)];
    var trees := deserialise(codes);
    assert |trees| == 1; 
    var expectedTree := DoubleNode(9, Leaf(6), DoubleNode(2, Leaf(5), SingleNode(4, Leaf(3))));
    assert trees[0] == expectedTree;
}

// Ex 4 

/*
lemma SerialiseLemma<V>(t : Tree<V>)
  ensures deserialise(serialise(t)) == t 
{
  // ToDo
}
*/

/*
function deserialiseAux<T>(codes: seq<Code<T>>, trees: seq<Tree<T>>): seq<Tree<T>>
  decreases codes
  requires |codes| > 0 || |trees| > 0
  ensures |deserialiseAux(codes, trees)| >= 0
{
  if |codes| == 0 then trees
  else
    if codes[0] == CLf(v) then deserialiseAux(codes[1..], trees + [Leaf(v)])
    else if codes[0] == CSNd(v) then deserialiseAux(codes[1..], trees[..|trees|-1] + [SingleNode(v, trees[|trees|-1])])
    else if codes[0] == CDNd(v) then deserialiseAux(codes[1..], trees[..|trees|-2] + [DoubleNode(v, trees[|trees|-1], trees[|trees|-2])])
    else trees
}
*/



