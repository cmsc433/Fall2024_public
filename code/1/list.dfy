/**

List

 */
datatype List<T> = Nil | Cons(head:T, tail:List<T>)

/**
Length of a list
 */
function length<T>(xs:List<T>):(l:nat){
  match xs {
    case Nil => 0
    case Cons(_, tail) => length(tail) + 1
  }
}
/**
Length of a list (Tail recursive)
 */
function lengthTailCall<T>(xs:List<T>, acc:nat):(l:nat)
  ensures lengthTailCall(xs,acc) == length(xs) + acc
{
  match xs {
    case Nil => acc
    case Cons(_, tail) => lengthTailCall(tail, acc+1)
  }
}

/**
Prove the tail recursive length equals the non-tail recursive length
 */
lemma length_correct<T>(xs:List<T>)
  ensures lengthTailCall(xs,0) == length(xs)
{}

/**
Length of a list (imperative)
 */
method length2<T>(xs:List<T>) returns (l:nat)
  ensures length(xs) == l  //postcondition
{
  var lst := xs;
  var len := 0;
  while lst != Nil
    decreases length(lst)
    invariant length(lst) + len == length(xs)
  {
    len := len + 1;
    lst := lst.tail;
  }
  return len;
}
/**
    get an item at the index from the list 
 */
function get<T>(xs:List<T>, index:nat):(v:T)
  requires index < length(xs)
  ensures contains(xs,v)
{
  match xs {
    case Cons(h,t)=>
      if index == 0 then h
      else get(t, index - 1)
  }
}
/**
Insert an item at index
 */
function insert<T>(xs:List<T>,v:T, index:nat):(l:List<T>)
  requires  index <= length(xs)
  ensures length(xs) + 1 == length(l)
  ensures get(l,index) == v //Equality-supporting type parameter T(==) is not needed for ghost context
{
  if index == 0 then Cons(v,xs)
  else Cons(xs.head, insert(xs.tail, v, index - 1))
}
/**
Check membership
 */
function contains<T(==)>(xs:List<T>, v:T):bool{
  match xs {
    case Nil => false
    case Cons(h,t) => v == h || contains(t,v)
  }
}
/**
Convert a list to q sequence
 */
function List2Seq<T>(xs:List<T>):(s:seq<T>)
  ensures length(xs) == |s|
  ensures forall i:nat:: i < length(xs) ==> get(xs,i) == s[i]
{
  match xs{
    case Nil => []
    case Cons(h,t)=>[h] + List2Seq(t)
  }

}
/**
Check if a sequence is a permutation of another sequence
 */
predicate IsPermutationOf<T(==)>(p: seq<T>, s: seq<T>) {
  multiset(p) == multiset(s)
}

/**
Check if a list is sorted
 */
predicate is_sorted(xs:List<int>){
  match xs{
    case Nil => true
    case Cons(_,Nil) => true
    case Cons(h1,Cons(h2,tail))=> if h1 > h2 then false
    else is_sorted (Cons(h2,tail))
  }
}

/**
Insert an item into a sorted list
 */
function insert_sorted(v:int, xs:List<int>):(l:List<int>)
  requires is_sorted(xs)
  ensures is_sorted(l)
  ensures length(l) == length(xs) + 1
  ensures contains(l,v)
  ensures !contains(xs,v)==> contains(l,v)
  ensures IsPermutationOf(List2Seq(Cons(v,xs)), List2Seq(l))
{
  match xs{
    case Nil =>Cons(v,Nil)
    case Cons(h,t)=>if v < h then Cons(v,xs)
    else Cons(h, insert_sorted(v,t))
  }

}
/**
Sort a list
 */
function insertion_sort(xs:List<int>):(l:List<int>)
  ensures is_sorted(l)
  ensures length(xs) == length(l)
  ensures IsPermutationOf(List2Seq(xs), List2Seq(l))
{
  match xs{
    case Nil => Nil
    case Cons(x, Nil) => xs
    case Cons(h,t)=>
      insert_sorted(h, insertion_sort(t))
  }

}

method Main(){
  var l := Cons(10,Cons(20,Cons(30,Cons (5,Nil))));
  var l2 := insertion_sort(l);
  print l,"\n";
  print l2,"\n";
}
