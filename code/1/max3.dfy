/**
calculate the max among 3 integers
 */
method Max3(a:int, b:int, c:int) returns (m:int)
ensures m >= a && m >= b && m >= c
ensures m ==a || m == b || m ==c
{
    if a >= b {
        m := a;
    }else{
        m := b;
    }
    if c >= m {
         m := c;
    }
    //m := m + 1;
}