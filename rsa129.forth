// RSA-129 crack FORTH implementation
// 114 381 625 757 888 867 669 235 779 976 146 612 010 218 296 721 242 362 562 561 842 935 706 935 245 733 897 830 597 123 563 958 705 058 989 075 147 599 290 026 879 543 541

// Simple math ops
: pow2+ ( n p -- n^p where p>1 )
// n p -- over
// n p n -- swap
// n n p -- 1 do
// n n -- over
// n n n -- *
// n n^i -- loop
// n n^p -- swap
// n^p n -- drop
// n^p
  over swap 1 do over * loop swap drop ;
: pow ( n p -- n^p )
// n p -- dup
// n p p -- 1 > if then
// n p -- pow2+
// n^p
// else
// n p -- drop
// n^1
  dup 1 > if pow2+ else drop then ;
: square ( n -- n^2) dup * ;
: ?odd ( n -- bool ) 1 and ;

// Miller-Rabin primality test (64-bit)
: a ( n -- 2 < a < n-2 ) 26 ;
: x ( n d -- x )
// n d -- over
// n d n -- a
// n d a -- swap
// n a d -- pow
// n a^d -- swap
// a^d n -- mod
// x
  over a swap pow swap mod ;

: p2fact ( n -- d r )
// n -- 64 0 do
// d -- dup
// d d -- ?odd
// d b -- if then
// d -- i
// d r -- leave
//
// d -- 2/
// d -- loop
  64 0 do dup ?odd if i leave then 2/ loop ;

: compx ( x n -- x )
// x n -- swap
// n x -- square
// n x^2 -- swap
// x^2 n -- mod
// x
  swap square swap mod ;

: ?composite ( n x r -- bool )
// n x r -- 1-
// n x r-1 -- 0 do
// n x -- over
// n x n -- compx
// n x -- dup
// n x x -- 1=
// n x b -- if
// n x -- 2drop 1
// 1 -- leave
//
// n x -- 2dup
// n x n x -- swap
// n x x n -- 1-
// n x x n-1 -- =
// n x b -- if then
// n x -- 2drop 0
// 0 -- leave
//
// n x -- loop
// n x -- 2drop
// -- 1
// 1
  1- 0 do over compx dup
    1= if 2drop 1 leave then
    2dup swap
    1- = if 2drop 0 leave then
  loop 2drop 1 ;

: ?prime ( n k -- bool )
// n k -- over
// n k n -- 1-
// n k n-1 -- p2fact
// n k d r -- rot
// n d r k -- 0 do
// n d r -- 2over
// n d r n d -- over
// n d r n d n - x
// n d r n x -- dup
// n d r n x x -- 1=
// n d r n x b -- if then
// n d r n x -- 2drop
// else
// n d r n x -- rot
// n d n x r -- ?composite
// n d -- !!!
// n d r -- loop
  over 1- p2fact rot
  0 do 2over x dup
    1= if 2drop else ?composite then
;
