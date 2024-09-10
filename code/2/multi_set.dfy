method test()
{
  assert (multiset{1,1,1} - multiset{1,1}) == multiset{1};
  assert multiset{1,2,3,1,4,1,5}  == multiset{1,1,1,2,3,4,5};
  assert {1} <= {1, 2} && {1, 2} <= {1, 2}; // subset
  assert multiset{1,2,3,1,4,1}  <= multiset{1,1,1,2,3,4,5};
  assert 5 in {1,3,4,5};
  assert (set x | x in {0,1,2}:: x + 0  ) == {0,1,2};
  assert {0,1,2}=={0*1,1*1,2*1};
  assert (set x | x in {0,1,2} :: x * 1 ) == {0,1,2};


}

method test2()
{
  assert multiset([1,1]) == multiset{1,1};
  assert multiset([1,1,1]) == multiset{1,1,1};
  assert multiset({1,2,3}) == multiset{1,2,3};
}
