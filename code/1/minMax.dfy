
method MinMax (x : int, y : int) returns (min : int, max : int)
{
    if (x < y) {
        min := x;
        max := y;
    }
    else {
        max := x;
        min := y;
    }
}

method Main ()
{
    var x : int, y : int;
    x, y := 5,3;
    x, y := MinMax(x, y);
    print "min = ", x, "\n";
    print "max = ", y, "\n";
}